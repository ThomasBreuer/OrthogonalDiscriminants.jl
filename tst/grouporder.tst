##  In finite characteristic:
##  Check for all characters whether the group order and the orders
##  of the two orthogonal groups in question admit a decision
##  which embedding is correct.
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "grouporder.tst" );

##
gap> result:= [];;
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      Append( result, OD_CheckGroupOrders( name ) );
>    od;
>  od;

##  Evaluate the result.
gap> OD_enter_values( result, "error" );

##
gap> STOP_TEST( "grouporder.tst" );

