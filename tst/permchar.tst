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
gap> result:= [];;
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      Append( result, OD_CheckPermutationCharacters( name ) );
>    od;
>  od;

##  Evaluate the 'result'.
gap> OD_enter_values( result, "error" );

##
gap> STOP_TEST( "permchar.tst" );

