##  Test that 'OD_PrintTable' does not run into errors.
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "print.tst" );

gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      # Construct the table but do not print it.
>      OD_PrintTable( name, false );
>    od;
>  od;

##
gap> STOP_TEST( "print.tst" );

