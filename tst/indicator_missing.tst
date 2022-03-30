
##  List the known (2-modular) tables for which
##  the Frobenius-Schur indicator is not known.
##
gap> SizeScreen( [ 72 ] );;
gap> START_TEST( "indicator_missing.tst" );

##
gap> result:= [];;
gap> for simpname in OD_NamesOfSimpleAtlasTables( "M" ) do
>    for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
>      t:= CharacterTable( name );
>      modt:= t mod 2;
>      if modt <> fail then
>        if not HasComputedIndicators( modt ) then
>          Add( result, [ name, "all" ] );
>        else
>          ind:= Indicator( modt, 2 );
>          miss:= PositionsProperty( ind, x -> not x in [ -1, 0, 1 ] );
>          if miss <> [] then
>            if ForAll( ind{ miss }, IsUnknown ) then
>              Add( result, [ name, miss ] );
>            else
>              Error( "strange indicator value" );
>            fi;
>          fi;
>        fi;
>      fi;
>    od;
>  od;

##
gap> for pair in result do
>      ConvertToRangeRep( pair[2] );
>      Print( pair[1], ": ", pair[2], "\n" );
>    od;
L2(49).2_1: [ 2 ]
L2(49).2_2: [ 2 .. 3 ]
L2(49).2_3: [ 2 ]
L2(81).2_1: [ 2 .. 3 ]
L2(81).4_1: [ 2 .. 3 ]
L2(81).2_2: [ 2 ]
L2(81).2_3: [ 2 ]
L2(81).4_2: [ 2 ]
R(27): [ 2, 13 .. 13 ]
R(27).3: [ 4, 21 .. 21 ]
ON.2: [ 5 .. 7 ]
O8-(3): [ 2 .. 32 ]
O8-(3).2_1: all
O8-(3).2_2: all
O8-(3).2_3: all
O10+(2): all
O10-(2): all
Co2: [ 12 ]
Fi22: all
Fi22.2: all
HN: [ 15, 18, 19 ]
HN.2: [ 4, 7, 8, 9, 10, 12, 13, 14 ]
F4(2): all
S10(2): all
Fi23: [ 2 .. 25 ]

##
gap> STOP_TEST( "indicator_missing.tst" );

