#############################################################################
##
#F  OD_SizeOfFieldOfDefinition( <vals>, <p> )
##
##  Assume that the condition holds for all Galois conjugates of entries in
##  <vals>.
##
OD_SizeOfFieldOfDefinition:= function( vals, p )
    local values, entry, q;

    # The first argument may be a list of cyclotomics.
    if   ForAll( vals, IsInt ) then
      return p;
    elif not ( IsList( vals ) and IsCyclotomicCollection( vals ) ) then
      Error( "<vals> must be a list of cyclotomics" );
    fi;

    values:= [];
    for entry in vals do
      if DenominatorCyc( entry ) mod p = 0 or
         Conductor( entry ) mod p = 0 then
        return fail;
      elif not IsRat( entry ) then
        Add( values, entry );
      fi;
    od;

    if ForAll( values, x -> IsCycInt( ( GaloisCyc( x, p ) - x ) / p ) ) then
      # All reductions lie in the prime field.
      return p;
    else
      # It is sufficient to look at powers of the map '*p'.
      q:= p;
      while true do
        q:= q * p;
        if ForAll( values,
                   x -> IsCycInt( ( GaloisCyc( x, q ) - x ) / p ) ) then
          return q;
        fi;
      od;
    fi;
end;


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
    local modtbl, p, tbl, name, pos, data, reduce, entry, value;

    modtbl:= UnderlyingCharacterTable( chi );
    p:= UnderlyingCharacteristic( modtbl );
    if p = 0 then
      tbl:= modtbl;
    else
      tbl:= OrdinaryCharacterTable( modtbl );
    fi;
    name:= Identifier( tbl );

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
      if IsSquareInFiniteField( Field( Rationals, chi ),
             FrobeniusCharacterValueFixed( AtlasIrrationality( value ), p ) ) then
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
      Error( "only for characteristic <> 2" );
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
##  Let <chi> be an absolutely irreducible ordinary character
##  that is not real-valued.
##  The function returns the orthogonal discriminant
##  of '<chi> + ComplexConjugate( <chi> )', as a cyclotomic integer.
##
OrthogonalDiscriminantIndicator0:= function( chi )
    local F, K, Q, d, d2, gen, delta, X, R, i;

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

    # Construct an element in F with real square.
    gen:= PrimitiveElement( F );
    delta:= ( gen - ComplexConjugate( gen ) )^2;

    return delta;
end;


#############################################################################
##
#F  OrthogonalDiscriminantFromIndexTwoSubgroup( <chi>, <s> )
##
##  Is the ordinary irreducible character <chi>
##  induced from a character of the index 2 subgroup whose character table is
##  <s>, or does it extend a character from <s>?
##
OrthogonalDiscriminantFromIndexTwoSubgroup:= function( chi, s )
    local tbl, classes, fus, rest, const, F, K, dchi, Q, sigma, x, d;

    tbl:= UnderlyingCharacterTable( chi );
    if Size( tbl ) <> 2 * Size( s ) then
      return fail;
    fi;
    classes:= SizesConjugacyClasses( tbl );
    fus:= GetFusionMap( s, tbl );
    rest:= chi{ fus };
    const:= Filtered( Irr( s ),
                x -> ( x[1] = chi[1] or 2 * x[1] = chi[1] ) and
                     ScalarProduct( s, x, rest ) <> 0 );
    F:= Field( Rationals, chi );
    K:= Field( Rationals, const[1] );

    if IsZero( chi{ Difference( [ 1 .. Length( classes ) ], fus ) } ) then
      # chi is induced from s
      Assert( 1, Length( const ) = 2 );
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
    else
      # 'chi' extends from 's' to 'tbl',
      # we can take the discriminant of the restriction.
      # The character field of chi can be larger than that
      # of the restriction;
      # in this case, we may find a nicer form (modulo squares in the
      # larger field).
      Assert( 1, Length( const ) = 1 );
      d:= OrthogonalDiscriminant( const[1] );
      if d <> fail and not IsInt( d ) then
        Info( InfoOD, 1,
              "chance to improve discriminant ", d, "?" );
      fi;
      return [ "ext", const[1], d ];
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
    local tbl, sname, s, result, rest, info;

    if chi[1] mod 2 = 1 then
      # We are not interested in characters of indicator + and odd degree.
      return 0;
    fi;

    tbl:= UnderlyingCharacterTable( chi );
    if UnderlyingCharacteristic( tbl ) <> 0 then
      Error( "only for ordinary characters" );
    fi;

    # Is there an element without eigenvalues \pm 1?
    result:= OrthogonalDiscriminantFromEigenvalues( chi );
    if result <> fail then
      return result;
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
           ClassPositionsOfKernel( GetFusionMap( s, tbl ) ) = [ 1 ] then
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
         ClassPositionsOfKernel( GetFusionMap( s, tbl ) ) = [ 1 ] then
        rest:= RestrictedClassFunction( chi, s );
        info:= OrthogonalDiscriminant( rest );
        if info <> fail then
          return info;
        fi;
      fi;
    od;

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

      if IsBound( galoisinfo[i] ) then
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
        # Provide the Galois info for later characters.
        FF:= CharacterField( irr[i] );
        for g in GaloisGroup( AsField( Intersection( F, FF ), FF ) ) do
          img:= OnTuples( irr[i], g );
          pos:= Position( irr, img );
          if pos > i then
            galoisinfo[ pos ]:= [ i, g!.galois ];
          fi;
        od;

        # Deal with this constituent.
        if ind[i] = 0 then
          # Find the complex conjugate character.
          pos:= Position( irr, ComplexConjugate( irr[i] ) );
          if i < pos then
            Add( result,
                 rec( position:= [ i, pos ],
                      value:= OrthogonalDiscriminantIndicator0( irr[i] ),
                      field:= Field( irr[i] + irr[ pos ] ),
                      why:= "pair of complex conjugate characters" ) );
          fi;
        elif ind[i] = -1 then
          # The discr. is 1, see [Braun/Nebe, Remark 3.1].
          Add( result,
               rec( position:= i,
                    value:= 1,
                    field:= Field( irr[i] ),
                    why:= "[Braun/Nebe, Remark 3.1]" ) );
        else
          # The value may be stored in the database.
          if ValueOption( "compute" ) <> true then
            val:= OrthogonalDiscriminantFromDatabase( irr[i] );
            if val <> fail then
              Add( result,
                   rec( position:= i,
                        value:= AtlasIrrationality( val ),
                        field:= Field( irr[i] ),
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
                      field:= Field( irr[i] ),
                      why:= "OrthogonalDiscriminantIndicatorPlus" ) );
          else
            Add( result,
                 rec( position:= i,
                      value:= fail,
                      field:= Field( irr[i] ),
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
    local info, F;

    info:= OrthogonalDiscriminantInfo( chi );
    if not IsList( info ) then
      return fail;
    elif Length( info ) = 1 then
      return info[1].value;
    elif ForAll( info, r -> r.value <> fail ) then
      # All values are known, we are done.
      return OD_SquareFreePart( Product( info, r -> r.value ) );
#T better form norms where Galois orbits occur.
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
    local G, F, M;

    G:= AtlasGroup( Character, chi );
    if G = fail then
#T the character cannot be identified yet;
#T check whether the available repres. allow us to conclude the value for chi;
#T e.g., if all of the given degree are in an orbit under group autom. then
#T we can take any of them!
      return fail;
    fi;
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
end;

