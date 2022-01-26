#############################################################################
##
#F  IsSquareInFiniteField( <F>, <val> )
##
##  Let <F> be a finite field of odd order $q$, or an odd prime power $q$,
##  and let <val> be either an element $x$ in the field with $q$ elements
##  or a cyclotomic that can be reduced to a nonzweo element $x$ in this
##  finite field, via 'FrobeniusCharacterValue'.
##
##  'IsSquareInFiniteField' returns 'true' if $x$ is a square in the field
##  with $q$ elements, and 'false' otherwise.
##
IsSquareInFiniteField:= function( F, val )
    local q, p;

    if IsField( F ) then
      q:= Size( F );
      p:= Characteristic( F );
    elif IsPrimePowerInt( F ) then
      q:= F;
      p:= PrimeBase( q );
    else
      Error( "<F> must be a finite field or a prime power" );
    fi;

    if p = 2 then
      Error( "<p> must be odd" );
    elif Characteristic( val ) = 0 then
      val:= FrobeniusCharacterValueFixed( val, p );
    fi;

    if val = fail or IsZero( val ) then
      Error( "the value cannot be reduced" );
    fi;

    val:= (q-1) / Order( val );
    if not IsInt( val ) then
      Error( "the value dos not lie in the field in question" );
    fi;

    return IsEvenInt( val );
end;


#############################################################################
##
#F  OD_SquareFreePart( <val> )
##
OD_SquareFreePart:= function( val )
    local sign;

    if IsInt( val ) then
      sign:= SignInt( val );
      val:= AbsInt( val );
      return Product( List( Filtered( Collected( Factors( val ) ),
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
    if IsBound( data.( p ) ) then
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
#F  OrthogonalDiscriminantIndicator0( <chi> )
##
##  Let <chi> be an absolutely irreducible ordinary character
##  that is not real-valued.
##  The function returns a string that encodes the orthogonal discriminant
##  of '<chi> + ComplexConjugate( <chi> )'.
##
##  (Apply 'AtlasIrrationality' in order to evaluate this string.)
##
OrthogonalDiscriminantIndicator0:= function( chi )
    local F, K, Q, d, d2, gen, delta, X, R, i;

    # If chi(1) is even then the discr. is 1.
    if chi[1] mod 2 = 0 then
      return "1";
    fi;

    # Let F be the character field (not real), and K the real subfield.
    F:= Field( Rationals, ValuesOfClassFunction( chi ) );
    K:= Field( List( GeneratorsOfField( F ), x -> x + ComplexConjugate(x) ) );

    # Find delta in K such that F = K(Sqrt(delta)).
    # Then the discr. is delta.
    if K = Rationals then
      # We find a negative integer (nice).
      return String( Quadratic( PrimitiveElement( F ) ).root );
    fi;

    # If F contains a quadratic field Q that is not in K
    # then choose the square root from Q, again get an integral delta.
    Q:= First( Subfields( F ),
               x -> Dimension(x) = 2 and not IsSubset( K, x ) );
    if Q <> fail then
      return String( Quadratic( PrimitiveElement( Q ) ).root );
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

    return CTblLib.StringOfAtlasIrrationality( delta );
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
        return [ "ind", const[1], "1" ];
      elif ForAny( GeneratorsOfField( K ),
                   x -> x <> ComplexConjugate( x ) ) then
        # 'rest' splits into two complex conjugates.
        # Theorem 6.10 (d) says that we compute the discriminant
        # from any of the constituents.
        return [ "ind", const[1],
                 OrthogonalDiscriminantIndicator0( const[1] ) ];
      elif const[1][1] mod 2 = 0 then
        dchi:= OrthogonalDiscriminant( const[1] );
        if dchi <> fail and dchi <> "0" then
          # Theorem 6.10 (b), we know the discr. of the restriction,
          # compute the norm.
          dchi:= AtlasIrrationality( dchi );
          if dchi in F then
            return [ "ind", const[1], "1" ];
          else
            return [ "ind", const[1],
                     CTblLib.StringOfAtlasIrrationality(
                         OD_SquareFreePart( Norm( K, F, dchi ) ) ) ];
          fi;
        fi;
      fi;

      if ForAny( Difference( [ 1 .. Length( classes ) ], fus ),
                     i -> OrdersClassRepresentatives( tbl )[i] = 2 ) then
        # split extension G:2
        # Theorem 6.10 (c)
        if const[1][1] mod 2 = 0 then
          return [ "ind", const[1], "1" ];
        fi;

        # Compute c \in F with K = F(Sqrt(c))
        Q:= First( Subfields( K ),
                   x -> Dimension( x ) = 2 and not IsSubset( F, x ) );
        if Q <> fail then
          return [ "ind", const[1],
                   String( Quadratic( PrimitiveElement( Q ) ).root ) ];
        else
          sigma:= First( PrimeResidues( Conductor( K ) ),
                    i -> ForAll( GeneratorsOfField( F ),
                           x -> GaloisCyc( x, i ) = x ) and
                                ForAny( GeneratorsOfField( K ),
                                  x -> GaloisCyc( x, i ) <> x ) );
          x:= PrimitiveElement( K );
          return [ "ind", const[1],
                   CTblLib.StringOfAtlasIrrationality(
                       ( x - GaloisCyc( x, sigma ) )^2 ) ];
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
      if d <> fail and not IsInt( AtlasIrrationality( d ) ) then
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
##  The function returns either 'fail' or a string that encodes
##  the orthogonal discriminant of <chi>.
##  (Apply 'AtlasIrrationality' in order to evaluate this string.)
##
OrthogonalDiscriminantIndicatorPlus:= function( chi )
    local tbl, sname, s, result;

    if chi[1] mod 2 = 1 then
      # We are not interested in characters of indicator + and odd degree.
      return "0";
    fi;

    tbl:= UnderlyingCharacterTable( chi );

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

    # We were not successful.
    return fail;
end;


#############################################################################
##
#F  OrthogonalDiscriminant( <chi> [: compute:= <val> ])
##
##  Let <chi> be an absolutely irreducible ordinary character.
##  The function returns either 'fail' or a string that encodes the
##  orthogonal discriminant of <chi>.
##
##  If the global option 'compute' is set to 'true' then stored values are
##  ignored,
##  otherwise the database of orthogonal discriminants is used if possible.
##
InstallGlobalFunction( OrthogonalDiscriminant, function( chi )
    local tbl, val, ind;

    if ValueOption( "compute" ) <> false then
      val:= OrthogonalDiscriminantFromDatabase( chi );
      if val <> fail then
        return val;
      fi;
    fi;

    tbl:= UnderlyingCharacterTable( chi );
    ind:= Indicator( tbl, [ chi ], 2 )[1];
    if ind = -1 then
      return "1";
    elif ind = 1 then
      return OrthogonalDiscriminantIndicatorPlus( chi );
    else
      # We can compute the OD of the sum 'chi + ComplexConjugate( chi )'
      # but 'chi' itself has no OD.
      return fail;
    fi;
end );


#############################################################################
##
#F  IsOrthogonallyStable( [<tbl>, ]<chi> )
##
##  The (ordinary or Brauer) character <chi> is defined to be
##  orthogonally stable if all its absolutely irreducible constituents
##  of indicator + have even degree.
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
    if UnderlyingCharacteristic( tbl ) = 0 then
      dec:= MatScalarProducts( tbl, Irr( tbl ), [ chi ] )[1];
    else
      dec:= Decomposition( Irr( tbl ), [ chi ], "nonnegative" )[1];
    fi;
    ind:= Indicator( tbl, 2 );
    deg:= List( Irr( tbl ), x -> x[1] );
    for i in [ 1 .. Length( ind ) ] do
      if ind[i] = 1 and deg[i] mod 2 = 1 and dec[i] <> 0 then
        return false;
      fi;
    od;

    return true;
end;

