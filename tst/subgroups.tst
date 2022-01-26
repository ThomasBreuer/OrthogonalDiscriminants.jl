##  Consistency check:
##  Are the stored modular ODs of liftable p-modular irreducible characters
##  compatible with the stored ordinary ODs of their lifts?
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "subgroups.tst" );

##
gap> result:= rec( verified:= [], new:= [], falsified:= [] );;
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      res:= OD_CheckSubgroups( name );
>      for nam in [ "verified", "new", "falsified" ] do
>        Append( result.( nam ), res.( nam ) );
>      od;
>    od;
>  od;

##  Evaluate the result.
gap> if Length( result.falsified ) > 0 then
>      Print( "#E  wrong stored values:\n" );
>      for entry in result.falsified do
>        Print( "#E  ", entry, "\n" );
>      od;
>    fi;

##
gap> STOP_TEST( "subgroups.tst" );

