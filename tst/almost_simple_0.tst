
##  Collect those ordinary characters 'chi' of groups G.2
##  for which the OD cannot be computed directly or derived
##  from the OD of a constituent of the restriction to an index 2 subgroup G.
##  That is,
##  'chi' has indicator +,
##  'chi' is induced from a character 'phi' of G,
##  'Field(phi) / Field(chi)' is a proper real field extension,
##  'phi(1)' is odd,
##  and G.2 is a non-split extension of G.
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "almost_simple_0.tst" );

##
gap> t:= "dummy";; n:= "dummy";; rest:= "dummy";; # avoid syntax error messages
gap> result:= [];;
gap> for simpname in OD_NamesOfSimpleAtlasTables( "M" ) do
>    for name in Filtered( OD_NamesOfAlmostSimpleAtlasTables( simpname ),
>                          x -> x <> simpname ) do
>      t:= CharacterTable( name );
>      n:= NrConjugacyClasses( t );
>      if t <> fail then
>        subtbls:= Filtered( List( NamesOfFusionSources( t ), CharacterTable ),
>            s -> s <> fail and
>                 2 * Size( s ) = Size( t ) and
>                 ClassPositionsOfKernel( GetFusionMap( s, t ) ) = [ 1 ] and
>                 not 2 in OrdersClassRepresentatives( t ){
>                              Difference( [ 1 .. n ],
>                                          GetFusionMap( s, t ) ) } );
>        if subtbls <> [] then
>          for i in [ 1 .. n ] do
>            chi:= Irr( t )[i];
>            if chi[1] mod 4 = 2 and Indicator( t, [ chi ], 2 )[1] = 1 then
>              for s in subtbls do
>                rest:= RestrictedClassFunction( chi, s );
>                const:= Filtered( Irr( s ),
>                                  x -> 2 * x[1] = rest[1]
>                                       and ScalarProduct( s, x, rest ) <> 0 );
>                if const <> [] then
>                  # 'chi' is induced from 's'.
>                  K:= Field( const[1] );
>                  F:= Field( rest );
>                  if F <> K and ForAll( GeneratorsOfField( K ),
>                                        x -> x = GaloisCyc( x, -1 ) ) then
>                    Add( result, [ Identifier( s ), Identifier( t ),
>                                   OD_CharacterName( t, i ), i ] );
>                  fi;
>                fi;
>              od;
>            fi;
>          od;
>        fi;
>      fi;
>    od;
>  od;

##
gap> result;
[ [ "L2(16).2", "L2(16).4", "34a", 15 ], 
  [ "L2(16).2", "L2(16).4", "34b", 16 ], 
  [ "U3(4).2", "U3(4).4", "78a", 10 ], 
  [ "U3(4).2", "U3(4).4", "78b", 11 ] ]

##
gap> STOP_TEST( "almost_simple_0.tst" );

