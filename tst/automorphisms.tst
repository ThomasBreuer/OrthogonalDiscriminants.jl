##  Consistency check:
##  Are the ODs constant on orbits under group automorphisms,
##  and do the ODs respect admissible field automorphisms?
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "automorphisms.tst" );

##  We cannot verify or falsify individual entries,
##  just detect inconsistencies (then messages are printed)
##  and derive missing values from known values.
gap> for simpname in OD_data.names do
>    autnames:= OD_NamesOfAlmostSimpleAtlasTables( simpname );
>    for name in autnames do
>      OD_CheckAutomorphisms( simpname, name );
>    od;
>  od;

##
gap> STOP_TEST( "automorphisms.tst" );

