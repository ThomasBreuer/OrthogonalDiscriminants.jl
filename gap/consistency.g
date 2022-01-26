#############################################################################
##
#F  OD_CheckPermutationCharacters( <name> )
##
##  Collect the information about irreducible characters 'chi' that are
##  relevant for the database, such that 'chi + 1' is a permutation
##  character.
##
OD_CheckPermutationCharacters:= function( name )
    local result, t, sname, s, pi, chi, pos, OD, entry, stored;

    result:= rec( verified:= [], new:= [], falsified:= [] );

    t:= CharacterTable( name );
    if t <> fail then
      for sname in NamesOfFusionSources( t ) do
        s:= CharacterTable( sname );
        if s <> fail and
           ClassPositionsOfKernel( GetFusionMap( s, t ) ) = [ 1 ] and
           IsOddInt( Size( t ) / Size( s ) ) then
          pi:= TrivialCharacter( s )^t;
          chi:= pi - TrivialCharacter( t );
          pos:= Position( Irr( t ), chi );
          if pos <> fail then
            OD:= OD_SquareFreePart( pi[1] );
            if chi[1] mod 4 = 2 then
              OD:= -OD;
            fi;
            OD:= String( OD );
            entry:= [ name, 0, pos, OD, "permchar" ];
            stored:= OrthogonalDiscriminantFromDatabase( chi );
            if stored = fail then
              Add( result.new, entry );
            elif stored = OD then
              Add( result.verified, entry );
            else
              Add( result.falsified, entry );
            fi;
          fi;
        fi;
      od;
    fi;

    return result;
end;


#############################################################################
##
#F  OD_CheckLiftableCharacters( <name> )
##
##  Collect the information about liftable p-modular irreducible characters
##  of the character table for <name>, for odd p:
##  Does the stored p-modular OD (O+ or O-) coincide with the OD obtained by
##  p-modular reduction of the ordinary OD?
##
OD_CheckLiftableCharacters:= function( name )
    local result, data, t, p, modt, rest, entry, chi, pos, ord,
          ordval, val, ODs, v, d, q, newentry;

    result:= rec( verified:= [], new:= [], falsified:= [] );

    t:= CharacterTable( name );
    if t = fail then
      return result;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    for p in Filtered( PrimeDivisors( Size( t ) ), IsOddInt ) do
      if IsBound( data.( p ) ) then
        modt:= t mod p;
        rest:= RestrictedClassFunctions( Irr( t ), modt );
        for entry in data.( p ) do
          chi:= Irr( modt )[ entry[2] ];
          pos:= Positions( rest, chi );
          if pos <> [] then
            # 'chi' lifts to characteristic zero
            ord:= Filtered( data.( 0 ), l -> l[2] in pos );
            if ord = [] then
              # The corresp. ordinary characters may be not real,
              # for example the degree 10 char. in A7 for p = 7.
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

                  # Compare.
                  newentry:= [ name, p, entry[2], ODs[1], "lift" ];
                  if ODs[1] = entry[3] then
                    Add( result.verified, newentry );
                  elif entry[3] = "?" then
                    Add( result.new, newentry );
                  else
                    Add( result.falsified, newentry );
                  fi;
                fi;
              fi;
            fi;
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
    local result, t, data, sname, sdata, s, cand, rest, i, tentry, res,
          restpos, sentry, sval, tval, chi, psi, opos;

    result:= rec( verified:= [], new:= [], falsified:= [] );

    t:= CharacterTable( name );
    if t = fail then
      return result;
    fi;

    data:= OD_Data( name );
    if data = fail then
      return result;
    fi;

    for sname in NamesOfFusionSources( t ) do
#T TODO: p > 0
      sdata:= OD_Data( sname );
      if sdata <> fail then
        s:= CharacterTable( sname );
        if ClassPositionsOfKernel( GetFusionMap( s, t ) ) =  [ 1 ] then
          cand:= Irr( t ){ List( data.0, l -> l[2] ) };
          rest:= RestrictedClassFunctions( cand, s );
          for i in [ 1 .. Length( cand ) ] do
            tentry:= data.0[i];

            # Check for induction from index two subgroups.
            res:= OrthogonalDiscriminantFromIndexTwoSubgroup( cand[i], s );
            if res <> fail and res[1] = "ind" then
              if tentry[3] = "?" then
                Add( result.new,
                     [ name, 0, data.0[i][2], res[3],
                       Concatenation( "ind(", sname, ")" ) ] );
              elif tentry[3] <> res[3] then
                Add( result.verified,
                     [ name, 0, data.0[i][2], res[3],
                       Concatenation( "ind(", sname, ")" ) ] );
              fi;
            fi;

            # Check for extension from subgroups.
            restpos:= Position( Irr( s ), rest[i] );
            sentry:= First( sdata.0, l -> l[2] = restpos );
            if sentry <> fail then
              # Compare the two values.
              sval:= sentry[3];
              tval:= tentry[3];
              chi:= Irr( t )[ tentry[2] ];
              psi:= Irr( s )[ restpos ];
              if sval = "?" then
                if tval <> "?" then
                  # We can take the value if Field(psi) contains Field(chi).
                  if IsSubset( Field( psi ), Field( chi ) ) then
                    Add( result.new,
                         [ sname, 0, restpos, tval,
                           Concatenation( "rest(", name, ")" ) ] );
                  fi;
                fi;
              elif tval = "?" then
                # We can take the value if Field(chi) contains Field(psi).
                if IsSubset( Field( chi ), Field( psi ) ) then
                  Add( result.new,
                       [ name, 0, tentry[2], sval,
                         Concatenation( "ext(", sname, ")" ) ] );
                fi;
              else
                if tval = sval then
                  # Both values are stored.
                  # Add a comment about verification only if no 'ext'/'rest'
                  # comments are available for the two directions.
                  opos:= Length( sentry );
                  if IsSubset( Field( psi ), Field( chi ) ) then
                    if PositionSublist( sentry[ opos ],
                           Concatenation( "rest(", name, ")" ) ) = fail then
                      Add( result.verified,
                           [ sname, 0, restpos, tval,
                             Concatenation( "rest(", name, ")" ) ] );
                    fi;
                  elif IsSubset( Field( chi ), Field( psi ) ) then
                    if PositionSublist( tentry[ opos ],
                           Concatenation( "ext(", sname, ")" ) ) = fail then
                      Add( result.verified,
                           [ name, 0, tentry[2], sval,
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
              fi;
            fi;
          od;
        fi;
      fi;
    od;

    return result;
end;

