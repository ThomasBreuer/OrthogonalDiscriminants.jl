##  Consistency check:
##  Are the stored modular ODs of liftable p-modular irreducible characters
##  compatible with the stored ordinary ODs of their lifts?
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "subgroups.tst" );

##  Collect and evaluate the result.
gap> result:= [];;
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      res:= OD_CheckSubgroups( name );
>      OD_enter_values( res, "error" );
>      Append( result, res );
>    od;
>  od;

##
gap> STOP_TEST( "subgroups.tst" );

