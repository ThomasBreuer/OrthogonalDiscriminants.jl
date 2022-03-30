
##  Collect those ordinary characters 'chi' with indicator o
##  in almost simple Atlas tables
##  for which the computed OD of 'chi + ComplexConjugate( chi )'
##  is not an integer.
##  (In these cases, one can think about a nicer form of the values.)
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "indicator_0.tst" );

##
gap> t:= "dummy";; # avoid syntax error messages
gap> result:= [];;
gap> for simpname in OD_NamesOfSimpleAtlasTables( "M" ) do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      t:= CharacterTable( name );
>      if t <> fail then
>        for i in [ 1 .. NrConjugacyClasses( t ) ] do
>          chi:= Irr( t )[i];
>          if Indicator( t, [ chi ], 2 )[1] = 0 then
>            discr:= OrthogonalDiscriminant( chi );
>            if not IsInt( discr ) then
>              Add( result,
>                   [ Identifier( t ), OD_CharacterName( t, i ), i,
>                     AtlasIrrationality( discr ) ] );
>            fi;
>          fi;
>        od;
>      fi;
>    od;
>  od;

##  Reformat the 'result'.
gap> irrats:= Set( result, x -> x[4] );
[ "-3b17-27", "-b5-3", "3b13-5", "3d73+2&3+4&5-16" ]
gap> List( irrats,
>          val -> Set( Filtered( result, l -> l[4] = val ), l -> l[1] ) );
[ [ "O10+(2)" ], [ "L2(32).5", "Sz(32).5", "U3(4)", "U3(9)" ], 
  [ "U3(4)" ], [ "L3(8)", "L3(8).3" ] ]

##
gap> STOP_TEST( "indicator_0.tst" );

