
##  Consistency check:
##  Are the stored modular ODs of liftable p-modular irreducible characters
##  compatible with the stored ordinary ODs of their lifts?
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "checkliftable.tst" );

##
gap> result:= [];;
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      Append( result, OD_CheckLiftableCharacters( name ) );
>    od;
>  od;

##  Evaluate the 'result'.
gap> OD_enter_values( result, "error" );

##
gap> STOP_TEST( "checkliftable.tst" );

