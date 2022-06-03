#############################################################################
##
#F  OD_CheckPermutationCharacters( <name> )
##
##  - Collect the information about irreducible characters 'chi' that are
##    relevant for the database, such that 'chi + 1' is a permutation
##    character of degree $n$.
##
##    The determinant of the bilinear form for 'chi' is 'n',
##    this yields a result in each characteristic not dividing $n$.
##    Here we check only characteristic zero, possible new information in
##    finite characteristic will be regarded as derived from the ordinary OD.
##
##  - Collect the information about orthogonal irreducible characters 'chi'
##    that are relevant for the database, such that 'chi(1) + 1' is the order
##    of a Sylow 'p'-subgroup P of the given group, for an odd prime 'p',
##    and 'chi + 1' vanishes on the nonidentity elements of P.
##
##    Then the restriction of 'chi' to P is orthogonally stable with
##    determinant 'chi(1) + 1'.
##
OD_CheckPermutationCharacters:= function( name )
    local result, t, sname, s, pi, chi, pos, OD, entry, stored, info, n,
          pair, p, q, pclasses;

    result:= [];

    t:= CharacterTable( name );
    if t <> fail then
      for sname in NamesOfFusionSources( t ) do
        s:= CharacterTable( sname );
        if s <> fail and
           ClassPositionsOfKernel( GetFusionMap( s, t ) ) = [ 1 ] and
           IsOddInt( Size( t ) / Size( s ) ) and
           not IsBrauerTable( s ) then
          pi:= TrivialCharacter( s )^t;
          chi:= pi - TrivialCharacter( t );
          pos:= Position( Irr( t ), chi );
          if pos <> fail then
            # 'chi' is rational.
            OD:= OD_SquareFreePart( pi[1] );
            if chi[1] mod 4 = 2 then
              OD:= -OD;
            fi;
            OD:= String( OD );
            Add( result, [ name, 0, pos, OD, "permchar" ] );
          fi;
        fi;
      od;
    fi;

    for pair in Collected( Factors( Size( t ) ) ) do
      p:= pair[1];
      q:= p^pair[2];
      if p <> 2 then
        pclasses:= PositionsProperty( OrdersClassRepresentatives( t ),
                       x -> x mod p = 0 and IsPrimePowerInt( x ) );
        for chi in Filtered( Irr( t ),
                       x -> x[1] + 1 = q and Set( x{ pclasses } ) = [ -1 ] ) do
          if Indicator( t, [ chi ], 2 ) = [ 1 ] then
            OD:= OD_SquareFreePart( q );
            if chi[1] mod 4 = 2 then
              OD:= -OD;
            fi;
            OD:= String( OD );
            pos:= Position( Irr( t ), chi );
            Add( result, [ name, 0, pos, OD, "permchar" ] );
          fi;
        od;
      fi;
    od;

    return result;
end;


#############################################################################
##
#F  OD_CheckEigenvalues( <name> )
##
##  Collect the information about irreducible characters 'chi' that are
##  relevant for the database, such that there is an element without
##  eigenvalues $\pm 1$ in <chi>.
##
OD_CheckEigenvalues:= function( name )
    local result, t, data, p, entry, modt, chi, OD;

    result:= [];

    t:= CharacterTable( name );
    if t = fail then
      return result;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    for p in List( Difference( RecNames( data ), [ "2" ] ), Int ) do
      for entry in data.( p ) do
        if p = 0 then
          modt:= t;
        else
          modt:= t mod p;
        fi;
        chi:= Irr( modt )[ entry[2] ];
        OD:= OrthogonalDiscriminantFromEigenvalues( chi );
        if OD <> fail then
          if p = 0 then
            OD:= CTblLib.StringOfAtlasIrrationality( OD );
          fi;
          Add( result, [ name, p, entry[2], OD, "ev" ] );
        fi;
      od;
    od;

    return result;
end;


#############################################################################
##
#F  CTBlocks_RowOrbitsFromColumnOrbits( <M>, <column_orbits> )
##
##  Let <A>M</A> be a <E>regular</E> matrix (this is not checked),
##  and let <A>column_orbits</A> be the set of orbits of some group <M>G</M>
##  of matrix automorphisms of <A>M</A> on the positions of columns,
##  see <Ref Func="MatrixAutomorphisms" BookName="ref"/>.
##  <P/>
##  <Ref Func="CTBlocks.RowOrbitsFromColumnOrbits"/> returns the set of
##  orbits of the corresponding action of <M>G</M> on the rows of <A>M</A>.
##
CTBlocks_RowOrbitsFromColumnOrbits:= function( M, column_orbits )
    local n, MM, omega, i, row_orbits, reps, poss, pos;

    # Compute the auxiliary matrix of orbit sums.
    n:= Length( M );
    MM:= List( [ 1 .. n ], i -> [] );
    for omega in column_orbits do
      for i in [ 1 .. n ] do
        Add( MM[i], Sum( M[i]{ omega } ) );
      od;
    od;

    # Compute the orbits on rows.
    row_orbits:= [];
    reps:= [];
    poss:= [];
    for i in [ 1 .. n ] do
      pos:= PositionSet( reps, MM[i] );
      if pos = fail then
        Add( row_orbits, [ i ] );
        Add( reps, MM[i] );
        Add( poss, Length( row_orbits ) );
        SortParallel( reps, poss );
      else
        Add( row_orbits[ poss[ pos ] ], i );
      fi;
    od;

    return row_orbits;
    end;


#############################################################################
##
#F  OD_OrbitsGroupAutomorphisms( <tbl>, <auttbls> )
##
OD_CommonOrbits:= function( orbs1, orbs2 )
    local orbs, orb, pos;

    orbs:= orbs1;
    for orb in orbs2 do
      pos:= PositionsProperty( orbs, x -> not IsEmpty( Intersection( x, orb ) ) );
      orbs:= Union( [ Union( orbs{ pos } ) ], orbs{ Difference( [ 1 .. Length( orbs ) ], pos ) } );
    od;
    return orbs;
end;


OD_OrbitsGroupAutomorphisms:= function( tbl, auttbls )
    local p, irr, orbs, auttbl, fus, poss, inv, colorbs, roworbs;

    p:= UnderlyingCharacteristic( tbl );
    irr:= Irr( tbl );
    orbs:= List( [ 1 .. Length( irr ) ], i -> [ i ] );
    for auttbl in auttbls do
      fus:= GetFusionMap( tbl, auttbl );
      if fus = fail then
        # Perhaps 'auttbl' does not count.
        if p = 0 then
          poss:= PossibleClassFusions( tbl, auttbl );
        else
          poss:= PossibleClassFusions( OrdinaryCharacterTable( tbl ),
                                       OrdinaryCharacterTable( auttbl ) );
        fi;
        if poss <> [] then
          # This criterion is sufficient for our almost simple tables.
          Error( "fusion from ", tbl, " to ", auttbl, " missing?" );
        fi;
      else
        inv:= InverseMap( fus );
        colorbs:= Union( Filtered( inv, IsList ),
                         List( Filtered( inv, IsInt ), x -> [ x ] ) );
        roworbs:= CTBlocks_RowOrbitsFromColumnOrbits( irr, colorbs );
        orbs:= OD_CommonOrbits( orbs, roworbs );
      fi;
    od;

    return orbs;
end;


#############################################################################
##
#F  OD_OrbitsFieldAutomorphisms( <tbl> )
##
##  Return the list of orbits of admissible field automorphisms
##  on the irreducible characters of <tbl>.
##  If <tbl> is a p-Brauer table then only p-Frobenius automorphisms are
##  admissible, otherwise all Galois automorphisms are admissible.
##
OD_OrbitsFieldAutomorphisms:= function( tbl )
    local orbs, p, fams, irr, done, i, phi, orb, gal, q, img, pos;

    orbs:= [];
    p:= UnderlyingCharacteristic( tbl );

    if p = 0 then
      # All Galois automorphisms are admissible.
      fams:= GaloisMat( Irr( tbl ) ).galoisfams;
      for i in [ 1 .. Length( fams ) ] do
        if fams[i] = 1 then
          Add( orbs, [ [ i ], [ 1 ] ] );
        elif IsList( fams[i] ) then
          Add( orbs, fams[i] );
        fi;
      od;
    else
      # Consider only Frobenius automorphisms.
      irr:= Irr( tbl );
      done:= List( irr, x -> false );
      for i in [ 1 .. Length( irr ) ] do
        if not done[i] then
          phi:= irr[i];
          orb:= [ i ];
          gal:= [ 1 ];
          q:= p;
          img:= GaloisCyc( phi, p );
          while img <> phi do
            pos:= Position( irr, img );
            Add( orb, pos );
            Add( gal, q );
            done[ pos ]:= true;
            img:= GaloisCyc( img, p );
            q:= q * p;
          od;
          Add( orbs, [ orb, gal ] );
        fi;
      od;
    fi;

    return orbs;
end;


#############################################################################
##
#F  OD_CheckAutomorphisms( <simpname>, <name> )
##
##  Characters that lie in one orbit under the action of group automorphisms
##  have the same OD (in any characteristic).
##  Characters that lie in one orbit under the action of field automorphisms
##  have Galois conjugate OD (in characteristic zero).
##  (We want to make sure that the chosen representatives are Galois
##  conjugate, in order to take products of ODs when forming norms.)
##
OD_CheckAutomorphisms:= function( simpname, name )
    local evalOD, result, data, tbl, auttbls, p, modtbl, modauttbls, data_p,
          roworbs, orb, orbdata, values, knownpos, knownvalues, F, propose,
          entry, l, newentry, pos, i, val;

    evalOD:= function(x)
      if x[3] = "?" then
        return "?";
      else
        return AtlasIrrationality( x[3] );
      fi;
    end;

    result:= [];

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    tbl:= CharacterTable( name );
    if tbl = fail then
      return result;
    fi;

    auttbls:= List( OD_NamesOfAlmostSimpleAtlasTables( simpname ),
                    CharacterTable );
    auttbls:= Filtered( auttbls, x -> Size( x ) mod Size( tbl ) = 0 and
                                      Size( x ) <> Size( tbl ) );

    for p in Concatenation( [ 0 ], PrimeDivisors( Size( tbl ) ) ) do
      if p = 0 then
        modtbl:= tbl;
        modauttbls:= auttbls;
      else
        modtbl:= tbl mod p;
        modauttbls:= List( auttbls, a -> a mod p );
      fi;

      if modtbl <> fail then
        modauttbls:= Filtered( modauttbls, a -> a <> fail );
        data_p:= data.( p );
        roworbs:= OD_OrbitsGroupAutomorphisms( modtbl, modauttbls );
        for orb in Filtered( roworbs, x -> Length( x ) > 1 ) do
          orbdata:= List( orb, i -> First( data_p, l -> l[2] = i ) );
          if ForAll( orbdata, x -> x = fail ) then
            # no orthogonal characters of even degree in the orbit
            continue;
          elif fail in orbdata then
            Error( "database not compatible with group automorphisms" );
          fi;
          if p = 0 then
            values:= List( orbdata, evalOD );
          else
            values:= List( orbdata, x -> x[3] );
          fi;
          knownpos:= PositionProperty( values, x -> x <> "?" );
          if knownpos = fail then
            # nothing known about this orbit
            continue;
          fi;
          knownvalues:= Set( Filtered( values, x -> x <> "?" ) );
          if Length( knownvalues ) <> 1 then
            # Check that the values are equal modulo squares;
            # note that we want the feature that taking products of
            # stored ODs yields norms if applicable.
            F:= Field( Rationals, [ knownvalues[1] ] );
            if ForAny( knownvalues{ [ 2 .. Length( knownvalues ) ] },
                 x -> SquareRootInNumberField( F,
                        x * knownvalues[1] ) = fail ) then
              # contradiction, but we cannot say which is wrong
              Print( "#E  ", name, ", p = ", p, ": values ",
                     knownvalues, " in an orbit under group automorphisms\n" );
            fi;
          else
            entry:= [ name, p,, values[ knownpos ],
                      Concatenation( "aut(", orbdata[ knownpos ][1], ")" ) ];
            for l in orbdata{ Positions( values, "?" ) } do
              newentry:= ShallowCopy( entry );
              newentry[3]:= l[2];
              Add( result, newentry );
            od;
          fi;
        od;

        roworbs:= OD_OrbitsFieldAutomorphisms( modtbl );
        for orb in Filtered( roworbs, x -> Length( x[1] ) > 1 ) do
          orbdata:= List( orb[1], i -> First( data_p, l -> l[2] = i ) );
          if ForAll( orbdata, x -> x = fail ) then
            # no orthogonal characters of even degree in the orbit
            continue;
          elif fail in orbdata then
            Error( "database not compatible with field automorphisms" );
          fi;
          if p = 0 then
            values:= List( orbdata, evalOD );
            if "?" in values then
              if Length( Set( values ) ) > 1 then
                Print( "#I  ", name, ", p = ", p, ": values ",
                       values, " in an orbit under field automorphisms:\n",
                       "#I  ", orbdata, "\n" );
              fi;
            elif ForAny( [ 1 .. Length( values ) ],
                   i -> GaloisCyc( values[1], orb[2][i] ) <> values[i] ) then
              # contradiction, but we cannot say which is wrong;
              # propose consistent values based on the first value
              propose:= StructuralCopy( orbdata );
              val:= AtlasIrrationality( propose[1][3] );
              for i in [ 2 .. Length( propose ) ] do
                propose[i][3]:= CTblLib.StringOfAtlasIrrationality(
                                    GaloisCyc( val, orb[2][i] ) );
              od;
              SortParallel( List( propose, l -> l[2] ), propose );
              Print( "#E  ", name, ", p = ", p, ": values ",
                     values, " in an orbit under field automorphisms\n",
                     "#E  replace as follows:\n", propose, "\n" );
            fi;
          else
            # The OD must be constant on orbits.
            values:= List( orbdata, x -> x[3] );
            if "O+" in values and "O-" in values then
              Print( "#E  ", name, ", p = ", p, ": values ",
                     values, " in an orbit under field automorphisms\n" );
            elif "?" in values and Length( Set( values ) ) > 1 then
              # propose consistent values based on the first value
              propose:= StructuralCopy( orbdata );
              Print( "#I  ", name, ", p = ", p, ": values ",
                     values, " in an orbit under field automorphisms:\n",
                     "#I  ", orbdata, "\n" );
            fi;
          fi;
        od;
      fi;
    od;

    return result;
end;


#############################################################################
##
#F  OD_CheckLiftableCharacters( <name> )
##
##  Collect the information about liftable p-modular irreducible characters
##  of the character table for <name>.
##  Does the stored p-modular OD (O+ or O-) coincide with the OD obtained by
##  p-modular reduction of the ordinary OD?
##  For odd p, we have O+ iff the p-modular reduction of the ordinary OD
##  is a square in the character field, and O- otherwise.
##  For p = 2, if the character in question is rational then
##  the ordinary OD is congruent to either 1 or -3 modulo 8,
##  and we have O+ in the former case, and O- in the latter.
##
OD_CheckLiftableCharacters:= function( name )
    local result, t, data, p, modt, rest, entry, chi, pos, q, i, F, N, qq,
          ord, ordval, val, ODs, v, d, newentry, entry0, OD0;

    result:= [];

    t:= CharacterTable( name );
    if t = fail then
      return result;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    for p in PrimeDivisors( Size( t ) ) do
      if not IsBound( data.( p ) ) then
        continue;
      fi;

      modt:= t mod p;
      rest:= RestrictedClassFunctions( Irr( t ), modt );
      for entry in data.( p ) do
        chi:= Irr( modt )[ entry[2] ];
        pos:= Positions( rest, chi );
        if pos <> [] then
          # 'chi' lifts to characteristic zero
          # (We are interested only in orthogonal lifts
          # for which we know the OD.)
          pos:= Intersection( pos, List( data.( 0 ), l -> l[2] ) );

          if p = 2 then
            # If the lift is rational we can relate the two ODs.
            ODs:= [];
            for i in [ 1 .. Length( pos ) ] do
              if ForAll( Irr( t )[ pos[i] ], IsInt ) then
                # The ordinary OD is congruent to 1 or -3 mod 8.
                entry0:= First( data.( 0 ), l -> l[2] = pos[i] );
                OD0:= entry0[3];
                if OD0 = "?" then
                  continue;
                fi;
                OD0:= Int( OD0 );
                if OD0 = fail then
                  Error( "nonintegral OD for rational character?" );
                elif OD0 mod 8 = 1 then
                  AddSet( ODs, "O+" );
                elif OD0 mod 8 = 5 then
                  AddSet( ODs, "O-" );
                else
                  Error( "wrong congruence for OD of rational character" );
                fi;
              fi;
            od;
            if Length( ODs ) > 1 then
              Error( "inconsistent reductions of ordinary OD" );
            elif Length( ODs ) <> 0 then
              Add( result, [ name, p, entry[2], ODs[1], "lift" ] );
            fi;
          else
            # Check that the 'p'-modular reduction of the character field
            # of the ordinary character (where we disregard the ramified part
            # of the extension) is an odd degree extension of the
            # character field of the Brauer character.
            q:= SizeOfFieldOfDefinition( chi, p );
            for i in [ 1 .. Length( pos ) ] do
              F:= Field( Irr( t )[ pos[i] ] );
              N:= Conductor( F );
              if N mod p = 0 then
                while N mod p = 0 do
                  N:= N / p;
                od;
                F:= Intersection( F, CF(N) );
              fi;
              qq:= OD_SizeOfFieldOfDefinition( GeneratorsOfField( F ), p );
              Assert( 1, q^LogInt( qq, q ) = qq );
              if IsEvenInt( LogInt( qq, q ) ) then
                Unbind( pos[i] );
              fi;
            od;
            pos:= Compacted( pos );
            ord:= Filtered( data.( 0 ), l -> l[2] in pos );
            if ord = [] then
              # The corresp. ordinary characters may be not real,
              # for example the degree 10 char. in A7 for p = 7.
              continue;
            elif ForAny( ord, x -> x[3] <> "?" ) then
              # We know the ordinary OD.
              ord:= Filtered( ord, x -> x[3] <> "?" );
              ordval:= List( ord, x -> AtlasIrrationality( x[3] ) );
              val:= List( ordval, x -> FrobeniusCharacterValueFixed( x, p ) );
              if ForAll( val, x -> x = fail ) then
                # We cannot compute the reduction,
                # either due to a missing Conway pol. or because the ordinary
                # OD cannot be reduced; the latter happens for J1, p = 5.
                if ForAll( ordval, v -> Conductor( v ) mod p = 0 ) then
                  Info( InfoOD, 1,
                        "ordinary ODs '", ordval, "' cannot be reduced mod ", p );
                else
                  Info( InfoOD, 1,
                        "no Conway polynomial for '", ordval, "' mod ", p );
                fi;
              else
                val:= Filtered( val, x -> x <> fail and not IsZero( x ) );
                # Zero can occur, e.g., for J1 and p = 7;
                # for L2(31) and p = 3, we have three lifts, two of them
                # reduce to zero.
                if val <> [] then
                  ODs:= [];
                  for v in val do
                    d:= DegreeFFE( v );
                    q:= SizeOfFieldOfDefinition( chi, p );
                    if ( Length( Factors( q ) ) / d ) mod 2 = 0 then
                      Add( ODs, "O+" );
                    else
                      # Compute whether 'v' is a square in the character field.
                      if ( (q-1) / Order( v ) ) mod 2 = 0 then
                        Add( ODs, "O+" );
                      else
                        Add( ODs, "O-" );
                      fi;
                    fi;
                  od;
                  if Length( Set( ODs ) ) > 1 then
                    Error( "inconsistent reductions of ordinary OD" );
                  fi;
                  Add( result, [ name, p, entry[2], ODs[1], "lift" ] );
                fi;
              fi;
            fi;
          fi;
        fi;
      od;
    od;

    return result;
end;


#############################################################################
##
#F  SizeOmega( <epsilon>, <d>, <q> )
##
##  If <epsilon> is +1 then return the order of \Omega^+( <d>, <q> ).
##  If <epsilon> is -1 then return the order of \Omega^-( <d>, <q> ).
##
SizeOmega:= function( epsilon, d, q )
    local m, s, q2, q2i, i;

    m  := d / 2;
    s  := 1;
    q2 := q^2;
    q2i:= 1;
    for i in [ 1 .. m-1 ] do
      q2i:= q2 * q2i;
      s  := s * (q2i-1);
    od;
    if q mod 2 = 1 then
      s:= s/2;
    fi;

    return q^(m*(m-1)) * (q^m-epsilon) * s;
end;


#############################################################################
##
#F  SizeOmegaModN( <d>, <q>, <N> )
##
##  (Do not form the huge group orders, divide actors off from <N>.)
##
SizeOmegaModN:= function( d, q, N )
    local m, exp, p, q2, q2i, i, g;

    m  := d / 2;
    exp:= 0;
    while N mod q = 0 do
      exp:= exp + 1;
      N:= N / q;
    od;
    p:= Factors( q )[1];
    if N mod p = 0 then
      exp:= exp + 1;
      while N mod p = 0 do
        N:= N / p;
      od;
    fi;
    if m*(m-1) < exp then
      # a group of order N does not embed in both candidates.
      return [ false, false ];
    fi;

    q2 := q^2;
    q2i:= 1;
    for i in [ 1 .. m-1 ] do
      q2i:= q2 * q2i;
      if i = 1 and q mod 2 = 1 then
        g:= Gcd( N, (q2i-1) / 2 );
      else
        g:= Gcd( N, q2i-1 );
      fi;
      N:= N / g;
      if N = 1 then
        # a group of order N may embed in both candidates
        return [ true, true ];
      fi;
    od;

    # embeds in + type?, embeds in - type?
    return [ (q^m-1) mod N = 0, (q^m+1) mod N = 0 ];
end;


#############################################################################
##
#F  OD_CheckGroupOrders( <name> )
##
##  Collect the information about p-modular abs. irreducible characters
##  of the character table for <name>:
##  Do the orders of the two possible orthogonal groups determine the
##  embedding?
##
OD_CheckGroupOrders:= function( name )
    local result, t, data, n, p, modt, entry, chi, q, modres, pos,
          OD, newentry;

    result:= [];

    t:= CharacterTable( name );
    if t = fail then
      return result;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    # The order of the subgroup that shall embed into the perfect group.
    n:= Sum( SizesConjugacyClasses( t ){ ClassPositionsOfSolvableResiduum( t ) } );
    for p in PrimeDivisors( Size( t ) ) do
      if IsBound( data.( p ) ) then
        modt:= t mod p;
        for entry in data.( p ) do
          chi:= Irr( modt )[ entry[2] ];
          q:= SizeOfFieldOfDefinition( chi, p );
          modres:= SizeOmegaModN( chi[1], q, n );
          pos:= Positions( modres, true );
          if Length( pos ) = 0 then
Error( "problem: cannot embed into an orthogonal group" );
          elif Length( pos ) = 1 then
            # decision!
            if pos[1] = 1 then
              OD:= "O+";
            else
              OD:= "O-";
            fi;
            Add( result, [ name, p, entry[2], OD, "order" ] );
          fi;
        od;
      fi;
    od;

    return result;
end;


#############################################################################
##
#F  OD_CheckSubgroups( <name> )
##
##  Collect the information about irreducible ordinary characters
##  of the character table for <name> that extend irreducible characters of
##  subgroups (not nec. with the same socle),
##  and about characters that are induced from index two subgroups:
##  Do the two ODs fit together?
##
OD_CheckSubgroups:= function( name )
    local result, ordt, data, sname, ords, p, t, s, cand, rest, i, tentry,
          res, sres, restpos, sentry, sval, sdata, tval, chi, psi, opos, d;

    result:= [];

    ordt:= CharacterTable( name );
    if ordt = fail then
      return result;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    for sname in NamesOfFusionSources( ordt ) do
      ords:= CharacterTable( sname );
      if ords = fail or IsBrauerTable( ords ) or
         ClassPositionsOfKernel( GetFusionMap( ords, ordt ) ) <>  [ 1 ] then
        continue;
      fi;
      for p in List( RecNames( data ), Int ) do
        if p = 0 then
          t:= ordt;
          s:= ords;
        else
          t:= ordt mod p;
          s:= ords mod p;
        fi;
        if t = fail or s = fail then
          continue;
        fi;

        cand:= Irr( t ){ List( data.( p ), l -> l[2] ) };
        rest:= RestrictedClassFunctions( cand, s );

        for i in [ 1 .. Length( rest ) ] do
          sval:= OrthogonalDiscriminant( rest[i] );
          if sval <> fail then
            # The restriction to 's' is orth. stable,
            # and we can compute its discriminant.
            if p = 0 then
              sval:= CTblLib.StringOfAtlasIrrationality( sval );
            elif sval = "O-" and IsEvenInt(
                  DegreeOverPrimeField( CharacterField( cand[i] ) ) /
                  DegreeOverPrimeField( CharacterField( rest[i] ) ) ) then
              sval:= "O+";
            fi;
            Add( result, [ name, p, data.( p )[i][2], sval,
                           Concatenation( "ext(", sname, ")" ) ] );
          else
            # Perhaps info from the database about 's' helps.
            sdata:= OD_Data( sname );
            if sdata <> fail then
              for i in [ 1 .. Length( cand ) ] do
                tentry:= data.( p )[i];

                # Check for induction from index two subgroups
                # (works only if the characteristic if different from 2).
                # Note that 'cand[i]' is a character of indicator +.
                res:= OrthogonalDiscriminantFromIndexTwoSubgroup( cand[i], s );
                if res <> fail and res[1] = "ind" then
                  if p = 0 then
                    sres:= CTblLib.StringOfAtlasIrrationality( res[3] );
                  else
                    sres:= res[3];
                  fi;
                  Add( result, [ name, p, data.( p )[i][2], sres,
                                 Concatenation( "ind(", sname, ")" ) ] );
                fi;

                # Check for extension from subgroups.
                restpos:= Position( Irr( s ), rest[i] );
                if IsBound( sdata.( p ) ) then
                  sentry:= First( sdata.( p ), l -> l[2] = restpos );
                else
                  sentry:= fail;
#T we can take an ordinary character!
                fi;
                if sentry <> fail then
                  # Compare the two values.
                  sval:= sentry[3];
                  tval:= tentry[3];
                  chi:= Irr( t )[ tentry[2] ];
                  psi:= Irr( s )[ restpos ];

                  if sval = "?" then
                    if tval <> "?" then
                      # We can take the value if the two character fields
                      # are equal.
                      # For p > 0, we can take a known "O-"
                      # (and we know that the field extension is odd).
                      if CharacterField( psi ) = CharacterField( chi ) then
                        Add( result, [ sname, p, restpos, tval,
                                       Concatenation( "rest(", name, ")" ) ] );
                      elif p > 0 and tval = "O-" then
                        if IsEvenInt(
                             DegreeOverPrimeField( CharacterField( chi ) )
                         / DegreeOverPrimeField( CharacterField( psi ) ) ) then
                          Error( "incompatible restrictions" );
                        fi;
                        Add( result, [ sname, p, restpos, "O-",
                                       Concatenation( "rest(", name, ")" ) ] );
                      fi;
                    fi;
                  elif tval = "?" then
                    # 'CharacterField(chi)' contains 'CharacterField(psi)'.
                    if p = 0 or
                       IsOddInt(
                           DegreeOverPrimeField( CharacterField( chi ) )
                         / DegreeOverPrimeField( CharacterField( psi ) ) ) then
                      # We take the value of 'psi' if 'p = 0' or if
                      # the field extension has odd degree.
                      Add( result, [ name, p, tentry[2], sval,
                                     Concatenation( "ext(", sname, ")" ) ] );
                    else
                      # We get "O+" if the field extension is even.
                      Add( result, [ name, p, tentry[2], "O+",
                                     Concatenation( "ext(", sname, ")" ) ] );
                    fi;
                  else
                    # Both values are stored.
                    if p = 0 then
                      if tval = sval then
                        # Add a comment about verification only if no 'ext'/'rest'
                        # comments are available for the two directions.
                        opos:= Length( sentry );
                        if IsSubset( Field( psi ), Field( chi ) ) then
                          if PositionSublist( sentry[ opos ],
                                 Concatenation( "rest(", name, ")" ) ) = fail then
                            Add( result, [ sname, p, restpos, tval,
                                           Concatenation( "rest(", name, ")" ) ] );
                          fi;
                        elif IsSubset( Field( chi ), Field( psi ) ) then
                          if PositionSublist( tentry[ opos ],
                                 Concatenation( "ext(", sname, ")" ) ) = fail then
                            Add( result, [ name, p, tentry[2], sval,
                                           Concatenation( "ext(", sname, ")" ) ] );
                          fi;
                        fi;
                      else
#T There may be a problem.
#T We could try to decide whether
#T they differ by a square (in some field) ...
#T And we should present some examples.
# Print( "different discr. for ", sentry, " and ", tentry, "\n" );
                      fi;
                    else  # p > 0
                      if sval = "O-" then
                        # 'tval' is "O-" iff the field ext. is odd
                        d:= DegreeOverPrimeField( CharacterField( chi ) )
                         / DegreeOverPrimeField( CharacterField( psi ) );
                        if ( tval = "O-" and IsEvenInt( d ) ) or
                           ( tval = "O+" and IsOddInt( d ) ) then
                          Error( "incompatible restrictions" );
                        fi;
                      elif sval = "O+" then
                        # 'tval' must be "O+"
                        if tval = "O-" then
                          Error( "incompatible restrictions" );
                        fi;
                      fi;
                    fi;
                  fi;
                fi;
              od;
            fi;
          fi;
        od;
      od;
    od;

    return result;
end;


#############################################################################
##
#F  OD_Check_AGR_Groups( <name> )
##
##  Run over those orthogonal irreducible Brauer characters 'chi'
##  in almost simple Atlas tables of <name> for which the AGR contains
##  generating matrices
##  (*and* the corresponding character can be identified).
##
OD_Check_AGR_Groups:= function( name )
    local result, t, data, p, modt, entry, chi, discr;

    result:= [];

    t:= CharacterTable( name );
    if t = fail then
      return result;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    for p in Concatenation( [ 0 ], PrimeDivisors( Size( t ) ) ) do
      if p = 0 then
        modt:= t;
      else
        modt:= t mod p;
      fi;
      if modt <> fail then
        for entry in data.( p ) do
          chi:= Irr( modt )[ entry[2] ];
          discr:= OrthogonalDiscriminantFromAGR( chi );
          if discr <> fail then
            if p = 0 then
              discr:= CTblLib.StringOfAtlasIrrationality( discr );
            else
              if discr = 1 then
                discr:= "O+";
              else
                discr:= "O-";
              fi;
            fi;
            Add( result, [ name, p, entry[2], discr, "AGR" ] );
          fi;
        od;
      fi;
    od;

    return result;
end;

# find characters of subgroups from which 'chi' is induced
OD_InducedFrom:= function( chi )
    local modtbl, p, ordtbl, res, maxname, s, mods, deg, cand;

    modtbl:= UnderlyingCharacterTable( chi );
    p:= UnderlyingCharacteristic( modtbl );
    if p = 0 then
      ordtbl:= modtbl;
    else
      ordtbl:= OrdinaryCharacterTable( modtbl );
    fi;

    res:= [];

    if not HasMaxes( ordtbl ) then
      # We give up.
      return res;
    fi;

    for maxname in Maxes( ordtbl ) do
      s:= CharacterTable( maxname );
      if p <> 0 then
        mods:= s mod p;
      else
        mods:= s;
      fi;
      deg:= chi[1] / Index( ordtbl, s );
      if IsInt( deg ) and mods <> fail then
        for cand in Irr( mods ) do
          if cand[1] = deg and InducedClassFunction( cand, modtbl ) = chi then
            Add( res, cand );
          fi;
        od;
      fi;
    od;

    return res;
end;

# If an orthogonal character is induced from an orthogonal character
# of a subgroup of odd index, and if the two character fields are equal
# then the orthogonal discriminants are equal.
OD_CheckImprimitiveCharacters:= function( name )
    local result, data, t, entry, chi, cand, OD, s, new;

    result:= [];
    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;
    data:= data.0;
    t:= CharacterTable( name );
    if t <> fail then
      for entry in data do
        chi:= Irr(t)[ entry[2] ];
        for cand in OD_InducedFrom( chi ) do
          s:= UnderlyingCharacterTable( cand );
          if CharacterField( chi ) = CharacterField( cand )
             and IsOddInt( Index( t, s ) ) then
            OD:= OrthogonalDiscriminant( cand );
            if OD <> fail then
              new:= [ name, 0, entry[2], String(OD),
                      Concatenation( "ind(", Identifier( s ), ")" ) ];
              if not new in result then
                Add( result, new );
              fi;
#T else
#T Error( "failure for ", [ name, entry, cand ], "\n" );
#T # check more cases whether we can improve!
            fi;
          fi;
        od;
      od;
    fi;

    return result;
end;


#############################################################################
##
#F  OD_CheckSymmetricGroup( <n> )
##
##  Compute the determinants of Gram matrices of invariant bilinear forms
##  of characters of the symmetric group of degree <n>
##  via the formula of Jantzen and Schaper.
##
OD_CheckSymmetricGroup:= function( n )
  local name, t, paras, result, entry, val, OD;

  name:= Concatenation( "S", String( n ) );
  t:= CharacterTable( name );
  paras:= List( CharacterParameters( t ), l -> l[2] );
  result:= [];
  for entry in OD_Data( Identifier( t ) ).0 do
    val:= GramDeterminant( paras[ entry[2] ] );
    OD:= Product( Filtered( val, x -> IsOddInt( x[2] ) ), x -> x[1] );
    if Irr( t )[ entry[2] ][1] mod 4 = 2 then
      OD:= - OD;
    fi;
    Add( result, [ Identifier( t ), 0, entry[2], String( OD ), "specht" ] );
  od;

  return result;
end;

