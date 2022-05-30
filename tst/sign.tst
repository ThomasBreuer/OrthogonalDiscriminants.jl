##  Check that the signs of the stored ODs are correct.
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "sign.tst" );

##
gap> for simpname in OD_data.names do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      data:= OD_Data( name ).0;
>      for entry in data do
>        OD:= Int( entry[3] );
>        if OD <> fail then
>          deg:= Int( Filtered( entry[1], IsDigitChar ) );
>          if ( deg mod 4 = 0 ) <> ( OD > 0 ) then
>            Print( "#E  ", name, ": ", entry, "\n" );
>          fi;
>        fi;
>      od;
>    od;
>  od;

##
gap> STOP_TEST( "sign.tst" );

