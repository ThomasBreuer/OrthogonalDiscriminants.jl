
##  Run over those orthogonal irreducible Brauer characters 'chi'
##  in almost simple Atlas tables for which the AGR contains
##  generating matrices.
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "from_AGR.tst" );

##
gap> result:= [];;
gap> for simpname in OD_NamesOfSimpleAtlasTables( "M" ) do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      Append( result, OD_Check_AGR_Groups( name ) );
>    od;
>  od;

##  Evaluate the 'result'.
gap> OD_enter_values( result, "error" );

##
gap> STOP_TEST( "from_AGR.tst" );

