##  Consistency check:
##  Are the ODs of ordinary irreducible characters 'chi' stored
##  where 'chi + 1' is a permutatation character,
##  and if yes then are they correct?
##  (If 'chi + 1' is a permutation character then 'chi' has
##  OD 'chi(1) + 1' if 'chi(1)' is a multiple of 4, and
##  OD '-chi(1)-1' if not.)
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "permchar.tst" );

##
gap> result:= rec( verified:= [], new:= [], falsified:= [] );;
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      res:= OD_CheckPermutationCharacters( name );
>      for nam in [ "verified", "new", "falsified" ] do
>        Append( result.( nam ), res.( nam ) );
>      od;
>    od;
>  od;

##  Evaluate the 'result'.
gap> if Length( result.falsified ) > 0 then
>      Print( "#E  wrong stored values:\n" );
>      for entry in result.falsified do
>        Print( "#E  ", entry, "\n" );
>      od;
>    fi;

##
gap> STOP_TEST( "permchar.tst" );

