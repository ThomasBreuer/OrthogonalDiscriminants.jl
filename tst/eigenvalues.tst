##  Consistency check (p <> 2 only):
##  Are the ODs of ordinary irreducible characters 'chi' stored
##  where an element 'g' exists on which 'chi' has no eigenvalues \pm 1,
##  and if yes then are they correct?
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "eigenvalues.tst" );

##
gap> result:= [];;
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      Append( result, OD_CheckEigenvalues( name ) );
>    od;
>  od;

##  Evaluate the 'result'.
gap> OD_enter_values( result, "error" );

##
gap> STOP_TEST( "eigenvalues.tst" );

