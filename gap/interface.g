#############################################################################
##
#A  OrthogonalDiscriminants( <tbl> )
##
##  Return a list <M>l</M> such that <M>l[i]</M> is bound if and only if
##  the <M>i</M>-th irreducible character of <A>tbl</A> has indicator
##  <C>+</C> and even degree.
##  The value at this position is <K>fail</K> if the orthogonal discriminant
##  of the character is not stored in the Atlas of Orthogonal Discriminants,
##  otherwise it is the string that is stored in this database.
##
DeclareAttribute( "OrthogonalDiscriminants", IsCharacterTable );

InstallMethod( OrthogonalDiscriminants,
    [ "IsCharacterTable" ],
    function( tbl )
    local p, name, result, data, ind, irr, i, reduce, entry, value, reduced;

    p:= UnderlyingCharacteristic( tbl );
    if p = 0 then
      name:= Identifier( tbl );
    else
      name:= Identifier( OrdinaryCharacterTable( tbl ) );
    fi;

    result:= [];
    data:= OD_Data( name );

    if data = fail then
      # Compute the positions of orthogonal irreducibles of even degree.
      # (If some indicators are not known then we regard them as orthogonal.)
      ind:= Indicator( tbl, 2 );
      irr:= Irr( tbl );
      for i in [ 1 .. Length( ind ) ] do
        if irr[i, 1] mod 2 = 0 and not ind[i] in [ -1, 0 ] then
          result[i]:= Unknown();
        fi;
      od;
      return result;
    elif IsBound( data.( p ) ) then
      reduce:= false;
      data:= data.( p );
    else
      # We know the value for 'p' iff we know it for '0'.
      reduce:= true;
      data:= data.( 0 );
    fi;

    for entry in data do
      if ( not reduce ) or entry[3] = "?" then
        result[ entry[2] ]:= entry[3];
      else
        # 'p' does not divide the group order,
        # we reduce the value from characteristic 0.
        value:= AtlasIrrationality( value );
        reduced:= FrobeniusCharacterValueFixed( value, p );
        if IsZero( reduced ) then
Error( "choose a better representative (use number theory)" );
        elif IsSquareInFiniteField( CharacterField( Irr( tbl )[ entry[2] ] ), reduced ) then
          return "O+";
        else
          return "O-";
        fi;
      fi;
    od;

    return result;
    end );


#############################################################################
##
#F  OD_SquareFreePart( <val> )
##
OD_SquareFreePart:= function( val )
    local sign;

    if IsRat( val ) and not IsInt( val ) then
      val:= NumeratorRat( val ) * DenominatorRat( val );
    fi;
    if IsInt( val ) then
      sign:= SignInt( val );
      return Product( List( Filtered( Collected( Factors( AbsInt( val ) ) ),
                                      pair -> IsOddInt( pair[2] ) ),
                            pair -> pair[1] ), sign );
    fi;
    return val;
end;


DeclareGlobalFunction( "OrthogonalDiscriminant" );


#############################################################################
##
#F  OrthogonalDiscriminantFromDatabase( <chi> )
##
##  Let <chi> be an (ordinary or Brauer) character.
##  If <chi> is an irreducible character such that
##  the database of orthogonal discriminants contains information about the
##  value or <chi> then this value (a string) is returned,
##  otherwise 'fail'.
##
OrthogonalDiscriminantFromDatabase:= function( chi )
    local modtbl, p, tbl, name, pos, data, reduce, entry, value, reduced;

    modtbl:= UnderlyingCharacterTable( chi );
    p:= UnderlyingCharacteristic( modtbl );
    if p = 0 then
      tbl:= modtbl;
    else
      tbl:= OrdinaryCharacterTable( modtbl );
    fi;
    name:= Identifier( tbl );
#T switch to a library table if necessary!

    pos:= Position( Irr( modtbl ), chi );
    if pos = fail then
      return fail;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return fail;
    elif IsBound( data.( p ) ) then
      reduce:= false;
      data:= data.( p );
    else
      # We know the value for 'p' iff we know it for '0'.
      reduce:= true;
      data:= data.( 0 );
    fi;

    entry:= First( data, l -> l[2] = pos );
    if entry = fail then
      return fail;
    fi;

    value:= entry[3];
    if value = "?" then
      return fail;
    elif reduce then
      # 'p' does not divide the group order,
      # we reduce the value from characteristic 0.
      value:= AtlasIrrationality( value );
      reduced:= FrobeniusCharacterValueFixed( value, p );
      if IsZero( reduced ) then
Error( "choose a better representative (use number theory)" );
      elif IsSquareInFiniteField( CharacterField( chi ), reduced ) then
        return "O+";
      else
        return "O-";
      fi;
    else
      return value;
    fi;
end;


#############################################################################
##
#F  OrthogonalDiscriminantFromEigenvalues( <chi> )
##
##  Let <chi> be a character in characteristic different from 2.
##  Return the OD of <chi> if there is a group element without eigenvalues
##  $\pm 1$ on <chi>,
##  otherwise return 'fail'.
##
##  The determinant of the invariant bilinear form is
##  det(rho(g)-rho(g^-1)) mod squares,
##  by Cor. 4.2 in "Orthogonal determinants of characters".
##
OrthogonalDiscriminantFromEigenvalues:= function( chi )
    local t, p, nccl, orders, ev, good, zeta, OD;

    t:= UnderlyingCharacterTable( chi );
    p:= UnderlyingCharacteristic( t );
    if p = 2 then
      return fail;
    fi;

    nccl:= NrConjugacyClasses( t );
    orders:= OrdersClassRepresentatives( t );
    ev:= List( [ 1 .. nccl ], i -> EigenvaluesChar( t, chi, i ) );
    good:= First( [ 1 .. nccl ], i -> ev[i][ orders[i] ] = 0 and
               ( orders[i] mod 2 = 1 or ev[i][ orders[i]/2 ] = 0 ) );
    if good = fail then
      # There is no such element.
      return fail;
    fi;

    # Compute the determinant.
    zeta:= E( orders[ good ] );
    ev:= ev[ good ];
    OD:= Product( [ 1 .. orders[ good ] ],
                  i -> ( zeta^i - zeta^-i )^ev[i], 1 );

    # Adjust the sign according to the degree, get the discriminant.
    if chi[1] mod 4 = 2 then
      OD:= -OD;
    fi;

    if p = 0 then
      # Reduce modulo squares.
      return OD_SquareFreePart( OD );
    elif IsSquareInFiniteField( CharacterField( chi ), OD ) then
      return "O+";
    else
      return "O-";
    fi;
end;


#############################################################################
##
#F  OrthogonalDiscriminantIndicator0( <chi> )
##
##  Let <chi> be an absolutely irreducible ordinary or Brauer character
##  that is not real-valued.
##  The function returns the orthogonal discriminant
##  of '<chi> + ComplexConjugate( <chi> )',
##  either as a cyclotomic integer (in characteristic zero)
##  or as one of the strings "O+", "O-" (in positive characteristic).
##
OrthogonalDiscriminantIndicator0:= function( chi )
    local tbl, p, F, K, Q, d, d2, gen, delta, X, R, i;

    # For Brauer characters, it may happen that the character fields of
    # 'chi' and 'chi + \overline{chi}' are equal,
    # and then Theorem 10 yields "O+".
    # Otherwise, apply Prop. 2.9.
    tbl:= UnderlyingCharacterTable( chi );
    p:= UnderlyingCharacteristic( tbl );
    if p > 0 then
      F:= CharacterField( chi );
      K:= CharacterField( chi + ComplexConjugate( chi ) );
      if F = K then
        # happens for example for L3(2), degree 3, lives over GF(2)
        return "O+";
      else
        # We have "O+" iff the degree of 'chi' is even.
        # (also for odd characteristic!)
        if IsEvenInt( chi[1] ) then
          return "O+";
        else
          return "O-";
        fi;
      fi;
    fi;

    # If chi(1) is even then the discr. is 1.
    if chi[1] mod 2 = 0 then
      return 1;
    fi;

    # Let F be the character field (not real), and K the real subfield.
    F:= Field( Rationals, ValuesOfClassFunction( chi ) );
    K:= Field( List( GeneratorsOfField( F ), x -> x + ComplexConjugate(x) ) );

    # Find delta in K such that F = K(Sqrt(delta)).
    # Then the discr. is delta.
    if K = Rationals then
      # We find a negative integer (nice).
      return Quadratic( PrimitiveElement( F ) ).root;
    fi;

    # If F contains a quadratic field Q that is not in K
    # then choose the square root from Q, again get an integral delta.
    Q:= First( Subfields( F ),
               x -> Dimension(x) = 2 and not IsSubset( K, x ) );
    if Q <> fail then
      return Quadratic( PrimitiveElement( Q ) ).root;
    fi;

    # Reduce from F to an extension of 2-power degree,
    # we can choose delta in an index 2 subfield of this field.
    d:= DegreeOverPrimeField( F );
    d2:= 1;
    while d mod 2 = 0 do
      d2:= 2 * d2;
      d:= d / 2;
    od;
    F:= First( Subfields( F ), x -> Dimension(x) = d2 );
    K:= Intersection( F, K );

    # Construct a nonreal element in F with real square.
    gen:= PrimitiveElement( F );
    delta:= ( gen - ComplexConjugate( gen ) )^2;

    return delta;
end;


#############################################################################
##
#F  OrthogonalDiscriminantFromIndexTwoSubgroup( <chi>, <s> )
##
##  Is the (ordinary or Brauer) irreducible character <chi>
##  (which is assumed to have even degree and indicator +)
##  induced from a character of the index 2 subgroup whose character table is
##  <s>, or does it extend a character from <s>?
##
OrthogonalDiscriminantFromIndexTwoSubgroup:= function( chi, s )
    local tbl, classes, fus, rest, irr, dec, const, F, K, p, dchi, Q, sigma,
          x, d;

    tbl:= UnderlyingCharacterTable( chi );
    if Size( tbl ) <> 2 * Size( s ) then
      return fail;
    fi;
    classes:= SizesConjugacyClasses( tbl );
    fus:= GetFusionMap( s, tbl );
    rest:= chi{ fus };
    irr:= Irr( s );
    dec:= Decomposition( irr, [ rest ], "nonnegative" )[1];
    const:= Irr( s ){ Filtered( [ 1 .. Length( dec ) ], i -> dec[i] <> 0 ) };
    F:= CharacterField( chi );
    K:= CharacterField( const[1] );
    p:= UnderlyingCharacteristic( tbl );

    if IsZero( chi{ Difference( [ 1 .. Length( classes ) ], fus ) } ) then
      # chi is induced from s
      if p = 2 then
        # Theorem 6.12 is not applicable.
        return fail;
      fi;
      Assert( 1, Length( const ) = 2 );
      if p = 0 then
        # Apply Thm. 6.10.
        if F = K then
          # The determinant is 1, according to Thm. 6.10 (a).
          if chi[1] mod 4 = 2 then
            return [ "ind", const[1], -1 ];
          else
            return [ "ind", const[1], 1 ];
          fi;
        elif ForAny( GeneratorsOfField( K ),
                     x -> x <> ComplexConjugate( x ) ) then
          # 'rest' splits into two complex conjugates.
          # Theorem 6.10 (d) says that we compute the discriminant
          # from any of the constituents.
          return [ "ind", const[1],
                   OrthogonalDiscriminantIndicator0( const[1] ) ];
        elif const[1][1] mod 2 = 0 then
          dchi:= OrthogonalDiscriminant( const[1] );
          if dchi <> fail and dchi <> 0 then
#T when can 0 occur?
            # Theorem 6.10 (b), we know the discr. of the restriction,
            # compute its norm. (The sign does not matter here.)
            return [ "ind", const[1],
                     OD_SquareFreePart( Norm( K, F, dchi ) ) ];
          fi;
        fi;

        if ForAny( Difference( [ 1 .. Length( classes ) ], fus ),
                       i -> OrdersClassRepresentatives( tbl )[i] = 2 ) then
          # split extension G:2
          # Theorem 6.10 (c); no sign change.
          if const[1][1] mod 2 = 0 then
            return [ "ind", const[1], 1 ];
          fi;

          # Compute c \in F with K = F(Sqrt(c)).
          # Here the sign must be changed.
          Q:= First( Subfields( K ),
                     x -> Dimension( x ) = 2 and not IsSubset( F, x ) );
          if Q <> fail then
            # We can choose c from a quadratic extension of the Rationals.
            return [ "ind", const[1],
                     - Quadratic( PrimitiveElement( Q ) ).root ];
          else
            # Compute a field autom. sigma of K that fixes F.
            sigma:= First( PrimeResidues( Conductor( K ) ),
                      i -> ForAll( GeneratorsOfField( F ),
                             x -> GaloisCyc( x, i ) = x ) and
                                  ForAny( GeneratorsOfField( K ),
                                    x -> GaloisCyc( x, i ) <> x ) );
            # Now x-x^sigma is in K\F, and the square is in F.
            x:= PrimitiveElement( K );
            return [ "ind", const[1], - ( x - GaloisCyc( x, sigma ) )^2 ];
          fi;
        else
          # non-split extension
          return fail;
        fi;
      else  # p > 0
        # Apply Thm. 6.12:
        # (c): If the constituent has even degree and indicator +,
        #      and if the group extension is split, we get "O+".
        # (d): If the constituent has even degree and indicator o,
        #      we get "O+".
        if IsEvenInt( const[1][1] ) then
          if ForAny( const[1], x -> x <> GaloisCyc( x, -1 ) ) then
            return [ "ind", const[1], "O+" ];
          elif Indicator( s, 2 )[ Position( Irr( s ), const[1] ) ] = 1 and
               ForAny( Difference( [ 1 .. Length( classes ) ], fus ),
                       i -> OrdersClassRepresentatives( tbl )[i] = 2 ) then
            return [ "ind", const[1], "O+" ];
          fi;
        fi;
      fi;
    else
      # 'chi' extends from 's' to 'tbl'.
      Assert( 1, Length( const ) = 1 );
      if p = 0 then
        # We can take the discriminant of the restriction.
        # The character field of 'chi' can be larger than that
        # of the restriction;
        # in this case (in characteristic 0),
        # we may find a nicer form (modulo squares in the larger field).
        d:= OrthogonalDiscriminant( const[1] );
        if d <> fail and p = 0 and not IsInt( d ) then
          Info( InfoOD, 1,
                "chance to improve discriminant ", d, "?" );
        fi;
        return [ "ext", const[1], d ];
      elif IsEvenInt( DegreeOverPrimeField( F ) / DegreeOverPrimeField( K ) ) then
        # The character field of 'chi' is an even extension of the
        # character field of 'const[1]', we get "O+".
        return [ "ind", const[1], "O+" ];
      else
        # We take the discriminant of the restriction.
        d:= OrthogonalDiscriminant( const[1] );
        if d <> fail then
          return [ "ind", const[1], d ];
        fi;
      fi;
    fi;

    return fail;
end;


#############################################################################
##
#F  OrthogonalDiscriminantIndicatorPlus( <chi> )
##
##  Let <chi> be an absolutely irreducible ordinary character of even degree
##  that has indicator +1.
##  The function returns either 'fail' or
##  the orthogonal discriminant of <chi>, as a cyclotomic integer.
##
OrthogonalDiscriminantIndicatorPlus:= function( chi )
    local tbl, sname, s, result, rest, info, ker, fus, fact, libfact, tr,
          pos, cand;

    if chi[1] mod 2 = 1 then
      # We are not interested in characters of indicator + and odd degree.
      return 0;
    fi;

    # Is there an element without eigenvalues \pm 1?
    # (works in characteristic different from 2)
    result:= OrthogonalDiscriminantFromEigenvalues( chi );
    if result <> fail then
      return result;
    fi;

    tbl:= UnderlyingCharacterTable( chi );
    if UnderlyingCharacteristic( tbl ) <> 0 then
      return fail;
    fi;

    # Is the character induced from a normal subgroup of index 2,
    # or does it extend a character from an index 2 subgroup?
    if Length( LinearCharacters( tbl ) ) mod 2 = 0 then
      # Run over the normal subgroups of index 2
      # whose character tables are available.
      for sname in NamesOfFusionSources( tbl ) do
        s:= CharacterTable( sname );
        if s <> fail and
           2 * Size( s ) = Size( tbl ) and
           ClassPositionsOfKernel( GetFusionMap( s, tbl ) ) = [ 1 ] and
           not IsBrauerTable( s ) then
          result:= OrthogonalDiscriminantFromIndexTwoSubgroup( chi, s );
          if result <> fail then
            return result[3];
          fi;
        fi;
      od;
    fi;

    # Is the restriction to a subgroup orthogonally stable such that
    # the discriminant can be computed?
    for sname in NamesOfFusionSources( tbl ) do
      s:= CharacterTable( sname );
      if s <> fail and
         ClassPositionsOfKernel( GetFusionMap( s, tbl ) ) = [ 1 ] and
         not IsBrauerTable( s ) then
        rest:= RestrictedClassFunction( chi, s );
        info:= OrthogonalDiscriminant( rest );
        if info <> fail then
          return info;
        fi;
      fi;
    od;

    # Try to factor out the kernel of the character.
    ker:= ClassPositionsOfKernel( chi );
    if Length( ker ) > 1 then
      fus:= First( ComputedClassFusions( tbl ),
                   r -> ClassPositionsOfKernel( r.map ) = ker );
      if fus <> fail and CharacterTable( fus.name ) <> fail then
        # The fusion to the factor is stored, take the library table.
        fact:= CharacterTable( fus.name );
        chi:= InducedClassFunctionsByFusionMap( tbl, fact, [ chi ], fus.map )[1];
        return OrthogonalDiscriminantIndicatorPlus( chi );
      else
        # Try to find a library table of the factor.
        # This table may store useful (subgroup) information.
        fact:= tbl / ker;
        chi:= InducedClassFunctionsByFusionMap( tbl, fact, [ chi ], GetFusionMap( tbl, fact ) )[1];
        libfact:= NameOfEquivalentLibraryCharacterTable( fact );
        if libfact <> fail then
          libfact:= CharacterTable( libfact );
          tr:= TransformingPermutationsCharacterTables( fact, libfact );
          pos:= Position( Irr( fact ), chi )^tr.rows;
          cand:= Orbit( AutomorphismsOfTable( libfact ),
                        Irr( libfact )[ pos ], Permuted );
          cand:= List( cand, OrthogonalDiscriminantIndicatorPlus );
          if Length( Set( cand ) ) > 1 then
Print( "#E  unsymmetric criteria?\n" );
          fi;
Print( "result from factoring out!\n" );
          return cand[1];
        fi;
      fi;
    fi;

    # We were not successful.
    return fail;
end;


#############################################################################
##
#F  OrthogonalDiscriminantInfo( [<tbl>, ]<chi> [: compute:= <val> ])
##

#T  Is chi allowed to be a Brauer character?

##  Return 'false' if <chi> is not orthogonally stable,
##  and 'fail' if not all indicators are known.
#T can happen only in char. 2
##
##  Otherwise return a list of records that correspond to the
##  real irreducible constituents of <chi>.
##
##  Each record has the components
##  - position:
##    value i means the i-th entry in Irr(t), where t is the table of <chi>;
##    value [i,j] means a pair of non-real irreducibles of t
##  - field:
##    the (maximal real subfield of the) character field of the constituent
##  - value:
##    'fail' means that the OD of the constituent is not yet known,
##    otherwise we have a cyclotomic integer
##  - why:
##    a string that describes how the value arises
##
OrthogonalDiscriminantInfo:= function( chi... )
    local tbl, p, irr, dec, ind, deg, F, result, galoisinfo, i, known, value,
          pos, FF, g, img, val;

    if Length( chi ) = 1 and IsClassFunction( chi[1] ) then
      tbl:= UnderlyingCharacterTable( chi[1] );
      chi:= ValuesOfClassFunction( chi[1] );
    else
      tbl:= chi[1];
      chi:= chi[2];
    fi;
    p:= UnderlyingCharacteristic( tbl );
    irr:= Irr( tbl );
    if UnderlyingCharacteristic( tbl ) = 0 then
      dec:= MatScalarProducts( tbl, irr, [ chi ] )[1];
    else
      dec:= Decomposition( irr, [ chi ], "nonnegative" )[1];
    fi;
    ind:= Indicator( tbl, 2 );
    deg:= List( irr, x -> x[1] );

    F:= CharacterField( chi, p );
    result:= [];

    # An entry [ i, k ] at position l means that irr[l] = irr[i]^{*k} holds.
    # (If the character field of 'irr[i]' is not contained
    # in the character field of 'chi' then make sure that
    # the discriminants of Galois conjugates are Galois conjugates
    # of discriminants, in order to get the norm when multiplying them.)
    galoisinfo:= [];

    for i in Filtered( [ 1 .. Length( ind ) ], x -> dec[x] <> 0 ) do
      if deg[i] mod 2 = 1 then
        if ind[i] = 1 then
          return false;
        elif not ( ind[i] in [ 0, -1 ] ) then
          # It may happen that the indicator is not known.
          return fail;
        fi;
      fi;

      # Consider only constituents with odd multiplicity.
      if dec[i] mod 2 = 0 then
        continue;
      fi;

      if p = 0 and IsBound( galoisinfo[i] ) then
        # Choose a Galois compatible discriminant.
        known:= First( result, r -> r.position = galoisinfo[i][1] );
        if known <> fail then
          if known.value = fail then
            value:= fail;
          else
            value:= GaloisCyc( known.value, galoisinfo[i][2] );
          fi;
          Add( result, rec( position:= i,
                            value:= value,
                            field:= known.field,
                            why:= Concatenation( "Galois conjugate ",
                                      String( galoisinfo[i] ) ) ) );
        else
          known:= First( result, r -> IsList( r.position ) and
                                      r.position[1] = galoisinfo[i][1] );
          pos:= Position( irr, ComplexConjugate( irr[i] ) );
          if i < pos then
            if known.value = fail then
              value:= fail;
            else
              value:= GaloisCyc( known.value, galoisinfo[i][2] );
            fi;
            Add( result, rec( position:= [ i, pos ],
                              value:= value,
                              field:= known.field,
                              why:= Concatenation( "Galois conjugate ",
                                        String( galoisinfo[i] ) ) ) );
          fi;
        fi;
      else
        if p = 0 then
          # Provide the Galois info for later characters.
          FF:= CharacterField( irr[i] );
          for g in GaloisGroup( AsField( Intersection( F, FF ), FF ) ) do
            img:= OnTuples( irr[i], g );
            pos:= Position( irr, img );
            if pos > i then
              galoisinfo[ pos ]:= [ i, g!.galois ];
            fi;
          od;
        fi;

        # Deal with this constituent.
        if ind[i] = 0 then
          # Find the complex conjugate character.
          pos:= Position( irr, ComplexConjugate( irr[i] ) );
          if i < pos then
            Add( result,
                 rec( position:= [ i, pos ],
                      value:= OrthogonalDiscriminantIndicator0( irr[i] ),
                      field:= CharacterField( irr[i] + irr[ pos ] ),
                      why:= "pair of complex conjugate characters" ) );
          fi;
        elif ind[i] = -1 then
          # The discr. is 1, see [Braun/Nebe, Remark 3.1].
          Add( result,
               rec( position:= i,
                    value:= 1,
                    field:= CharacterField( irr[i] ),
                    why:= "[Braun/Nebe, Remark 3.1]" ) );
        else
          # The value may be stored in the database.
          if ValueOption( "compute" ) <> true then
            val:= OrthogonalDiscriminantFromDatabase( irr[i] );
            if val <> fail then
              Add( result,
                   rec( position:= i,
                        value:= AtlasIrrationality( val ),
                        field:= CharacterField( irr[i] ),
                        why:= "stored in the database" ) );
              continue;
            fi;
          fi;

          # Try.
          val:= OrthogonalDiscriminantIndicatorPlus( irr[i] );
          if val <> fail then
            Add( result,
                 rec( position:= i,
                      value:= val,
                      field:= CharacterField( irr[i] ),
                      why:= "OrthogonalDiscriminantIndicatorPlus" ) );
          else
            Add( result,
                 rec( position:= i,
                      value:= fail,
                      field:= CharacterField( irr[i] ),
                      why:= "sorry ..." ) );
          fi;
        fi;
      fi;
    od;

    return result;
end;


#############################################################################
##
#F  OrthogonalDiscriminant( <chi> [: compute:= <val> ])
##
##  Let <chi> be a (not nec. absolutely irreducible) ordinary character.
##  The function returns either 'fail' or the orthogonal discriminant of
##  <chi>.
##
##  If the global option 'compute' is set to 'true' then stored values are
##  ignored,
##  otherwise the database of orthogonal discriminants is used if possible.
##
InstallGlobalFunction( OrthogonalDiscriminant, function( chi )
    local info, dchi, mult, r, dpsi;

    info:= OrthogonalDiscriminantInfo( chi );
    if not IsList( info ) then
      return fail;
    elif Length( info ) = 1 then
      return info[1].value;
    elif ForAll( info, r -> r.value <> fail ) then
      # All values are known, we are done.
      if UnderlyingCharacteristic( UnderlyingCharacterTable( chi ) ) = 0 then
        # Note that in characteristic zero, compatible discriminants are chosen
        # for Galois conjugate constituents, thus 'Product' computes norms.
        return OD_SquareFreePart( Product( info, r -> r.value ) );
      else
        # Do not form norms but take the inverse of the degrees of the
        # field extensions as weights.
        # (For 'chi' over GF(p), k values 'O-' for constituents over GF(p^k)
        # together yield one 'O-' for 'chi'.)
        dchi:= DegreeOverPrimeField( CharacterField( chi ) );
        mult:= 0;
        for r in Filtered( info, r -> r.value = "O-" ) do
          dpsi:= DegreeOverPrimeField( r.field );
          if dchi mod dpsi = 0 then
            if IsOddInt( dchi / dpsi ) then
              mult:= mult + 1;
            fi;
          else
            mult:= mult + Gcd( dchi, dpsi ) / dpsi;
          fi;
        od;
        if not IsInt( mult ) then
          Error( "strange restriction" );
        elif IsOddInt( mult ) then
          return "O-";
        else
          return "O+";
        fi;
      fi;
    fi;

    Info( InfoOD, 2,
          "fails because the OD of some constituent is unknown" );
    return fail;
end );


#############################################################################
##
#F  IsOrthogonallyStable( [<tbl>, ]<chi> )
##
##  The (ordinary or Brauer) character <chi> is defined to be
##  orthogonally stable if
##  - <chi> is orthogonal, that is, <chi> is real,
##    and all its absolutely irreducible constituents of indicator -
##    have even multiplicity
##  - and all its absolutely irreducible constituents of indicator +
##    have even degree.
##
##  For Brauer characters in characteristic 2, the indicator of some
##  irreducible constituent of <chi> may be unknown;
##  in this case, 'fail' is returned.
##
IsOrthogonallyStable:= function( chi... )
    local tbl, dec, ind, deg, i;

    if Length( chi ) = 1 and IsClassFunction( chi[1] ) then
      tbl:= UnderlyingCharacterTable( chi[1] );
      chi:= ValuesOfClassFunction( chi[1] );
    else
      tbl:= chi[1];
      chi:= chi[2];
    fi;

    if ForAny( chi, x -> GaloisCyc( x, -1 ) <> x ) then
      return false;
    fi;

    if UnderlyingCharacteristic( tbl ) = 0 then
      dec:= MatScalarProducts( tbl, Irr( tbl ), [ chi ] )[1];
    else
      dec:= Decomposition( Irr( tbl ), [ chi ], "nonnegative" )[1];
    fi;

    ind:= Indicator( tbl, 2 );
    deg:= List( Irr( tbl ), x -> x[1] );

    for i in [ 1 .. Length( ind ) ] do
      if ind[i] = -1 then
        if dec[i] mod 2 <> 0 then
          return false;
        fi;
      elif ind[i] = 1 then
        if dec[i] <> 0 and deg[i] mod 2 <> 0 then
          return false;
        fi;
      elif ind[i] <> 0 then
        # It may happen that the indicator is not known.
        # The value can be 1 or -1, so test both conditions.
        if dec[i] mod 2 <> 0 then
          return fail;
        elif dec[i] <> 0 and deg[i] mod 2 <> 0 then
          return fail;
        fi;
      fi;
    od;

    return true;
end;


#############################################################################
##
#F  OrthogonalDiscriminantFromGenerators( <F>, <gens> )
##
##  Let <F> be a field (a finite field or a number field),
##  and let <gens> be a list of generators of a (finite) matrix group $G$,
##  defined over <F>.
##  If $G$ leaves a non-degenerate orthogonal form invariant then
##  'OrthogonalDiscriminantFromGenerators' returns its orth. discriminant.
##
OrthogonalDiscriminantFromGenerators:= function( F, gens )
    local G, i, cand, j, elm, det, M;

    if IsGroup( gens ) then
      G:= gens;
      gens:= GeneratorsOfGroup( G );
    elif IsList( gens ) then
      G:= Group( gens );
    else
      Error( "<gens> must be a list of generaors or a group" );
    fi;

    if Characteristic( F ) = 0 then
      # Try to compute the determinant of the invariant form
      # without computing the form.
      i:= 0;
      while i < 100 do
        cand:= List( [ 1 .. 3 ], x -> PseudoRandom( G ) );
        if ForAll( cand, x -> Order( x ) <> 2 ) then
          cand:= List( cand, x -> x - x^-1 );
          for j in [ 1 .. 10 ] do
            elm:= List( cand, x -> Random( [ 1, -1 ] ) ) * cand;
            det:= OD_SquareFreePart( DeterminantMat( elm ) );
            if not IsZero( det ) then
              if DimensionOfMatrixGroup( G ) mod 4 = 2 then
                det:= - det;
              fi;
              return det;
            fi;
          od;
        fi;
      od;
    else
      # Use the MeatAxe function.
      M:= GModuleByMats( gens, F );
      return MTX.OrthogonalSign( M );
    fi;
end;


#############################################################################
##
#F  OrthogonalDiscriminantFromAGR( <chi> )
##
OrthogonalDiscriminantFromAGR:= function( chi )
    local G, F, tbl, p, ordtbl, name, infos, signs, r, M;

    G:= AtlasGroup( Character, chi );
    if G <> fail then
      # The character was already identified.
      F:= AtlasRepInfoRecord( G ).ring;
      if IsIntegers( F ) then
        F:= Rationals;
      fi;

      # In odd characteristic, we have to make sure that 'F' is
      # an odd degree extension of the character field.
      # In characteristic 2, we accept only representations over the
      # character field.
      # In characteristic 0, we can work with field extensions
      # because the determinant of the form in question lies in the
      # character field.
      if F <> CharacterField( chi ) then
        if Characteristic( F ) = 2 or
           ( IsOddInt( Characteristic( F ) ) and IsEvenInt( Dimension( F ) / Dimension( CharacterField( chi ) ) ) ) then
  Print( "AGR repres. with strange character field: ", AtlasRepInfoRecord( G ), "\n" );
          return fail;
        fi;
      fi;
      return OrthogonalDiscriminantFromGenerators( F, G );
    fi;

    # Check whether the available representations allow us to
    # identify 'chi' and to conclude the value for 'chi',
    # using some heuristics.
    tbl:= UnderlyingCharacterTable( chi );
    p:= UnderlyingCharacteristic( tbl );
    if p = 0 then
      ordtbl:= tbl;
    else
      ordtbl:= OrdinaryCharacterTable( tbl );
    fi;
    name:= Identifier( ordtbl );
    infos:= AllAtlasGeneratingSetInfos( name, Characteristic, p,
                Dimension, chi[1] );
    if Length( infos ) = 0 or not chi in Irr( tbl ) or p = 0 then
      return fail;
#T are there cases with p = 0 that would be interesting?
    fi;

    if Number( Irr( tbl ), x -> x[1] = chi[1] ) = 1 then
#T or if unique up to group automorphisms?
#T and take only those infos that have the correct character field? (careful)
      signs:= [];
      for r in infos do
        G:= AtlasGroup( r );
        if G <> fail then
          F:= AtlasRepInfoRecord( G ).ring;
          if IsIntegers( F ) then
            F:= Rationals;
          fi;

          if F <> CharacterField( chi ) then
            if Characteristic( F ) = 2 or
               ( IsOddInt( Characteristic( F ) ) and IsEvenInt( Dimension( F ) / Dimension( CharacterField( chi ) ) ) ) then
              Print( "AGR repres. with strange character field: ", AtlasRepInfoRecord( G ), "\n" );
              continue;
            fi;
          fi;
          M:= GModuleByMats( GeneratorsOfGroup( G ), F );
          if not MTX.IsAbsolutelyIrreducible( M ) then
            continue;
          fi;
          Add( signs, MTX.OrthogonalSign( M ) );
        fi;
      od;
      if Length( signs ) = 1 then
        # We have found the sign of an abs. irreducible module of degree
        # 'chi[1]', and there is exactly one such irr. character for 'G'.
        return signs[1];
      elif Length( signs ) > 1 then
        Error( "how can this happen?" );
      fi;
    fi;

    return fail;
end;


#############################################################################
##
#F  OD_PrintTable( <tbl> )
#F  OD_PrintTable( <chi> )
#F  OD_PrintTable( <name>[, false] )
##
##  <chi>: ordinary irreducible orthogonal character
##  If 'false' is given as second argument then the table gets constructed
##  but not printed.
##
OD_PrintTable:= function( tbl, print... )
    local data, characters, ord, primes, modtbls, header, positions, result,
          i, chipos, chi, red, resulti, j, p, stable, dec, pos, res1, res2,
          k, ppos, cc, bl, colwidth, hline, l;

    # Just compute the table without printing it if 'print' is 'false'
    # (for testing purposes).
    print:= not ( Length( print ) = 1 and print[1] = false );

    if IsString( tbl ) then
      tbl:= CharacterTable( tbl );
      data:= OD_Data( Identifier( tbl ) );
      characters:= Irr( tbl ){ List( data.0, l -> l[2] ) };
    elif IsClassFunction( tbl ) then
      characters:= [ tbl ];
      tbl:= UnderlyingCharacterTable( chi );
    elif IsCharacterTable( tbl ) then
      data:= OD_Data( Identifier( tbl ) );
      characters:= Irr( tbl ){ List( data.0, l -> l[2] ) };
    else
      Error( "<tbl> must be an (identifier of an) ordinary character table ",
             "or an ordinary irreducible character" );
    fi;

    ord:= Size( tbl );
    primes:= PrimeDivisors( ord );
    modtbls:= List( primes, p -> tbl mod p );

    header:= Concatenation( Identifier( tbl ), ":  ", StringPP( ord ) );
    if print then
      Print( "\n", header, "\n",
             RepeatedString( "-", Length( header ) ), "\n\n" );
    fi;

    positions:= List( characters, chi -> Position( Irr( tbl ), chi ) );

    header:= Concatenation( [ "i", "chi", "K", "disc" ],
                            List( primes, String ) );

    result:= [ header ];
    for i in [ 1 .. Length( positions ) ] do
      chipos:= positions[i];
      chi:= characters[i];
      resulti:= [ [ String( chipos ),
                    OD_CharacterName( tbl, chipos ),
                    StringOfCharacterField( chi ),
                    First( data.0, l -> l[2] = chipos )[3] ],
                  [ "", "", "", "" ] ];
      if chi[1] mod 4 = 2 and resulti[1][4] = "?" then
        resulti[1][4]:= "-?";
      fi;
      for j in [ 1 .. Length( primes ) ] do
        p:= primes[j];
        if modtbls[j] = fail then
          # We do not know the 'p'-Brauer table.
          Add( resulti[1], "?" );
          Add( resulti[2], "" );
        else
          red:= RestrictedClassFunction( chi, modtbls[j] );
          stable:= IsOrthogonallyStable( red );
          if stable = true then
            dec:= Decomposition( Irr( modtbls[j] ), [ red ], "nonnegative" )[1];
            pos:= PositionsProperty( dec, IsOddInt );
            res1:= [];
            res2:= [];
            for k in pos do
              ppos:= First( data.( p ), r -> r[2] = k );
              if ppos <> fail then
                # must be indicator '+'
                Add( res1, OD_CharacterName( modtbls[j], k ) );
                Add( res2, ppos[3] );
              else
                cc:= Position( Irr( modtbls[j] ),
                               ComplexConjugate( Irr( modtbls[j] )[k] ) );
                if cc > k then
                  # indicator 'o'
                  Add( res1, Concatenation( OD_CharacterName( modtbls[j], k ),
                               Filtered( OD_CharacterName( modtbls[j], cc ),
                                         IsAlphaChar ) ) );
                  Add( res2, OrthogonalDiscriminantIndicator0(
                                 Irr( modtbls[j] )[k] ) );
                elif cc = k then
                  # indicator is *unknown*;
                  # note that indicator '-' (disc is "O+") cannot occur here
                  Add( res1, OD_CharacterName( modtbls[j], k ) );
                  Add( res2, "?" );
                fi;
              fi;
            od;
            Add( resulti[1], JoinStringsWithSeparator( res1, "+" ) );
            Add( resulti[2], JoinStringsWithSeparator( res2, ", " ) );
          elif stable = fail then
            # The indicator for at least one constituent is not known.
            Add( resulti[1], "?" );
            Add( resulti[2], "" );
          else
            bl:= PrimeBlocks( tbl, p );
            if bl.defect[ bl.block[ chipos ] ] = 1 then
              Add( resulti[1], "(def. 1)" );
            else
              Add( resulti[1], "" );
            fi;
            Add( resulti[2], "" );
          fi;
        fi;
      od;
      Append( result, resulti );
    od;

    colwidth:= List( TransposedMat( result ),
                     c -> Maximum( List( c, Length ) ) );

    hline:= RepeatedString( "-",
                Sum( colwidth ) + 3 * Length( colwidth ) - 1 );
    for i in [ 1 .. Length( result ) ] do
      l:= result[i];
      if print then
        for j in [ 1 .. Length( l ) ] do
          Print( String( l[j], colwidth[j] ), " | " );
        od;
        Print( "\n" );
        if i mod 2 = 1 then
          Print( hline, "\n" );
        fi;
      fi;
    od;
end;

