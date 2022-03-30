##  Run over all tables, check whether they can be displayed
##  with 'BrowseOD'.
##  An example where "?" occurs in p-modular reductions
##  (OD as well as character values):
##  'BrowseOD( "J1", 97 );'
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "browse.tst" );

##
gap> for name in OD_data.names do
>      t:= CharacterTable( name );
>      if t <> fail then
>        for p in Concatenation( Filtered( [ 2 .. 50 ], IsPrimeInt ), [ 0 ] ) do
>          BrowseData.SetReplay( "Q" );
>          BrowseOD( name, p );
>        od;
>      fi;
>    od;

##
gap> BrowseData.SetReplay( false );

##
gap> STOP_TEST( "browse.tst" );

