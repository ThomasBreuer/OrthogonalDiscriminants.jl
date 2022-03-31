#############################################################################
##
#F  OD_SplitString( <string>, <sep> )
##
OD_SplitString:= function( string, sep )
    local open, result, start, i;

    open:= 0;
    result:= [];
    start:= 0;
    for i in [ 1 .. Length( string ) ] do
      if string[i] = '(' then
        open:= open + 1;
      elif string[i] = ')' then
        open:= open - 1;
      elif string[i] in sep and open = 0 then
        Add( result, string{ [ start+1 .. i-1 ] } );
        start:= i;
      fi;
    od;
    Add( result, string{ [ start+1 .. Length( string ) ] } );

    return result;
end;


#############################################################################
##
#F  BrowseOD( <name>[, <p>] )
##
##  Show a Browse table for the OD data of the group with name <name>,
##  for characteristic <p> (a prime or zero, the default is zero).
##
##  The table has the following structure.
##
##  The column labels show the character table header, that is,
##  centralizer orders, power maps, and class names.
##
##  The row labels show, for the relevant irreducible characters
##  (those of even degree that have indicator +),
##  the numbers in the Atlas table and the known information about the
##  orthogonal discriminants, where the latter needs one or two columns.
##
##  - If <p> divides the group order then there is one column "OD" which
##    contains the values "O+" and "O-" from the database.
##
##  - If <p> is zero then there is one column "OD" which shows the
##    orthogonal discriminants in characteristic zero, in Atlas notation.
##
##  - If <p> is a prime not dividing the group order then there are
##    two columns, one with the orthogonal discriminants in characteristic
##    zero and one with the values "O+" and "O-", according to whether or not
##    the reduction to characteristic <p> is a square in the character field
##    or not.
##    (A value "?" in the second column although a known value is shown in
##    the first column means that computing the <p>-modular reduction failed
##    due to an unknown Conway polynomial.)
##
##  The table values themselves are the character degrees in column "1A"
##  and either the character values (if <p> is zero) or their <p>-modular
##  reductions (if <p> is nonzero) in the remaining columns;
##  in the latter case, the values are written as polynomials in 'z',
##  which are representatives modulo the ideal spanned by the Conway
##  polynomial.
##
##  In all cases, unknown values and  unknown <p>-modular reductions
##  are shown as "?".
##
BrowseOD:= function( name, p... )
    local ordtbl, tbl, ind, cnr, chars, OD, ODred, id, pos, simpleid, i, val,
          d, q, charsmodp, chi, l, pol, c, charnames, nam, table, powermap;

    ordtbl:= CharacterTable( name );
    if Length( p ) = 0 then
      p:= 0;
    else
      p:= p[1];
    fi;
    if p = 0 then
      tbl:= ordtbl;
    else
      tbl:= ordtbl mod p;
      if tbl = fail then
        Print( "#E  the ", p, "-modular table of ", name,
               " is not available\n" );
        return;
      fi;
    fi;

    # Restrict the irreducibles to the ones with even degree
    # and indicator '+'.
    if p = 2 then
      ind:= ComputedIndicators( tbl );
      if not IsBound( ind[2] ) then
        Print( "#E  the indicators of the ", p, "-modular table of ", name,
               " are not available\n" );
        return;
      fi;
      ind:= ind[2];
    else
      ind:= Indicator( tbl, Irr( tbl ), 2 );
    fi;
    cnr:= Filtered( [ 1 .. NrConjugacyClasses( tbl ) ],
            i -> Irr( tbl )[i][1] mod 2 = 0 and ind[i] = 1 );
    chars:= Irr( tbl ){ cnr };

    # Fetch the known OD values
    OD:= ListWithIdenticalEntries( Length( cnr ), "?" );
    id:= Identifier( ordtbl );
    pos:= Position( id, '.' );
    if pos = fail then
      simpleid:= id;
    else
      simpleid:= id{ [ 1 .. pos-1 ] };
    fi;
    if IsBound( OD_data.( simpleid ) ) and
       IsBound( OD_data.( simpleid ).( id ) ) and
       ( IsBound( OD_data.( simpleid ).( id ).( p ) ) or
         ( p <> 0 and Size( tbl ) mod p <> 0 ) ) then
      if p = 0 then
        # Show the stored OD as is.
        OD:= List( OD_data.( simpleid ).( id ).( 0 ), l -> l[3] );
      elif Size( tbl ) mod p = 0 then
        # just fetch
        OD:= List( OD_data.( simpleid ).( id ).( p ), l -> l[3] );
      else
        # Compute the p-modular reductions of the stored values for char. zero.
        # We assume that p is odd.
        OD:= List( OD_data.( simpleid ).( id ).( 0 ), l -> l[3] );
        ODred:= ShallowCopy( OD );
        for i in [ 1 .. Length( OD ) ] do
          if OD[i] <> "?" then
            val:= FrobeniusCharacterValueFixed( AtlasIrrationality( OD[i] ), p );
            if val = fail then
              ODred[i]:= "?";
            else
if IsZero( val ) then
  Error( "zero!" );
fi;
              d:= DegreeFFE( val );
              q:= SizeOfFieldOfDefinition( chars[i], p );
              if ( Length( Factors( q ) ) / d ) mod 2 = 0 then
                ODred[i]:= "O+";
              else
                # Compute whether 'val' is a square in the character field.
                if ( (q-1) / Order( val ) ) mod 2 = 0 then
                  ODred[i]:= "O+";
                else
                  ODred[i]:= "O-";
                fi;
              fi;
            fi;
          fi;
        od;
      fi;
    fi;

    if p = 0 then
      charsmodp:= List( chars, chi -> List( chi, String ) );
    else
      # Compute the polynomials describing the character values.
      charsmodp:= [];
      for chi in chars do
        l:= [ String( chi[1] ) ];
        for i in [ 2 .. Length( chi ) ] do
          pol:= ReductionToFiniteField( chi[i], p );
          if pol = fail then
            l[i]:= "?";
          else
            pol:= pol[1];
            c:= CoefficientsOfLaurentPolynomial( pol );
            if Length( c[1] ) = 0 then
#T GAP error, will be fixed in the next version ...
              l[i]:= "0";
            else
              l[i]:= StringUnivariateLaurent( FamilyObj( pol ),
                         List( c[1], IntFFE ), c[2], "z");
            fi;
          fi;
        od;
        Add( charsmodp, l );
      od;
    fi;

    # choice of characters and character names
    charnames:= List( cnr, i -> Concatenation( "X.", String( i ) ) );

    # prepare class names
    nam:= ClassNames( tbl, "ATLAS" );

    # Construct the browse table.
    table:= rec(
      work:= rec(
        align:= "ct",
        header:= [ Identifier( tbl ) ],
        main:= charsmodp,
        m:= Length( chars ),
        n:= NrConjugacyClasses( tbl ),

        # The labels lists will be filled below.
        labelsRow:= [ List( charnames,
                        x -> rec( rows:= [ String( x ) ], align:= "l" ) ) ],
        labelsCol:= [],
        sepLabelsRow:= [ "" ],
        sepLabelsCol:= [],
        sepCol:= [ " " ],
        corner:= [],
      ),
      dynamic:= rec(
        sortFunctionForTableDefault:= BrowseData.CompareCharacterValues,
        sortFunctionForColumnsDefault:= BrowseData.CompareCharacterValues,
        sortFunctionForRowsDefault:= BrowseData.CompareCharacterValues,
      ),
    );

    # print OD (and ODred if available) instead of indicator
    Add( table.work.sepLabelsRow, " " );
    Add( table.work.labelsRow, OD );
    if IsBound( ODred ) then
      Add( table.work.sepLabelsRow, " " );
      Add( table.work.labelsRow, ODred );
    fi;
    table.work.labelsRow:= TransposedMat( table.work.labelsRow );
    Append( table.work.sepLabelsRow, [ "" ] );

    # Add centralizers themselves as column labels.
    Add( table.work.sepLabelsCol, " " );
    Add( table.work.corner, [ "" ] );
    if IsBound( ODred ) then
      Add( table.work.corner, [ "" ] );
    fi;
    Add( table.work.labelsCol,
         List( SizesCentralizers( tbl ), String ) );

    # three lines: power maps, p' part, and class names
    powermap:= CambridgeMaps( tbl );
    Append( table.work.sepLabelsCol, [ " ", "", "", " " ] );
    Append( table.work.labelsCol, [ powermap.power,
                                    powermap.prime,
                                    powermap.names ] );
    if IsBound( ODred ) then
      Append( table.work.corner, [ Concatenation( [ "" ], [ "" ], [ "p " ] ),
                                   Concatenation( [ "" ], [ "" ], [ "p'" ] ) ] );
      Add( table.work.corner, [ "", "OD", "" ] );
    else
      Append( table.work.corner, [ Concatenation( [ "" ], [ "p " ] ),
                                   Concatenation( [ "" ], [ "p'" ] ) ] );
      Add( table.work.corner, [ "", "OD" ] );
    fi;

    # Check whether at least one character and at least the degree column
    # fit into the window (the footer needs at most three lines).
    # If the window is not high enough for the column labels then hide them
    # and forbid expanding them.
    table.work.minyx:= [ t -> BrowseData.MinimalWindowHeight( t ),
                         BrowseData.MinimalWindowWidth ];

    # Show the table.
    NCurses.BrowseGeneric( table );
end;


#############################################################################
##
#F  BrowseODData()
##
BindGlobal( "BrowseODData", function()
    local mat, simpname, data, name, p, entry, table;

    mat:= [];
    for simpname in OD_data.names do
      data:= OD_data.( simpname );
      for name in OD_NamesOfAlmostSimpleAtlasTables( simpname ) do
        for p in Set( RecNames( data.( name ) ), Int ) do
          for entry in data.( name ).( p ) do
            Add( mat, [ rec( rows:= [ name ], align:= "l" ),
                        String( p ),
                        rec( rows:= [ entry[1] ], align:= "l" ),
                        entry[3],
                        rec( rows:= [ Last( entry ) ], align:= "l" ) ] );
          od;
        od;
      od;
    od;

    # Construct the browse table.
    table:= rec(
      work:= rec(
        align:= "ct",
        header:= t -> BrowseData.HeaderWithRowCounter( t,
                        "Orthogonal Discriminants of Atlas Groups",
                        Length( mat ) ),
        CategoryValues:= function( t, i, j )
          if   j = 2 then
            return [ t.work.main[ i/2 ][ j/2 ].rows[1] ];
          elif j = 4 then
            return [ Concatenation( "p = ", t.work.main[ i/2 ][ j/2 ] ) ];
          elif j = 6 then
            return [ Concatenation( "chi = ", t.work.main[ i/2 ][ j/2 ].rows[1] ) ];
          elif j = 8 then
            return [ Concatenation( "OD = ", t.work.main[ i/2 ][ j/2 ] ) ];
          elif j = 10 then
            return List( OD_SplitString( t.work.main[ i/2 ][ j/2 ].rows[1], "," ),
                         x -> Concatenation( "source = ", x ) );
          else
            Error( "this should not happen" );
          fi;
        end,

        main:= mat,

        labelsRow:= [],
        labelsCol:= [ [ rec( rows:= [ "G" ], align:= "l" ),
                        rec( rows:= [ "p" ], align:= "r" ),
                        rec( rows:= [ "chi" ], align:= "l" ),
                        rec( rows:= [ "OD" ], align:= "r" ),
                        rec( rows:= [ "source" ], align:= "l" ),
                      ] ],
        sepLabelsCol:= "=",
        sepRow:= "-",
        sepCol:= [ "| ", " | ", " | ", " | ", " | ", " |" ],

        SpecialGrid:= BrowseData.SpecialGridLineDraw,
      ),
    );

    BrowseData.SetSortParameters( table, "column", 1,
      [ "add counter on categorizing", "yes" ] );

    BrowseData.SetSortParameters( table, "column", 5,
      [ "hide on categorizing", "no",
        "add counter on categorizing", "yes" ] );

    # Show the browse table.
    NCurses.BrowseGeneric( table );
    end );


#############################################################################
##
##  Add the Browse application to the list shown by `BrowseGapData'.
##
BrowseGapDataAdd( "OD Data", BrowseODData, "\
the current contents of the Orthogonal Discriminants for Atlas groups, \
shown in a browse table whose columns contain the group names, \
the characteristic, the names of the characters in question, the OD values, \
and the source of the data" );

