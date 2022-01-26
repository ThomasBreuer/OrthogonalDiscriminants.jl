##############################################################################
##
##  Start GAP and read this file,
##  in order to load the Orthogonal Discriminants stuff.
##
if LoadPackage( "JSON", false ) <> true then
  Error( "the JSON package is needed in order to read data files" );
fi;

OD_pkgdir:= CallFuncList(
    function()
    local currfile, currdir;

    currfile:= INPUT_FILENAME();
    currdir:= currfile{ [ 1 .. PositionSublist( currfile, "init.g" )-1 ] };
    if Length( currdir ) = 0 then
      return DirectoryCurrent();
    else
      return Directory( currdir );
    fi;
    end, [] );


##############################################################################
##
##  Switch on diagnostic output if wanted.
##
DeclareInfoClass( "InfoOD" );

SetInfoLevel( InfoOD, 1 );


##############################################################################
##
##  Load the data.
##
#V  OD_data
##
##  <Var Name="OD_Data"/> is a record that stores the currently known
##  information about orthogonal discriminants of Atlas groups.
##  The component names are
##
##  - 'names':
##    the list of <Ref Attr="Identifier"/> values of the character tables of
##    simple Atlas groups for which OD data are available
##    (ordered by group order),
##
##  - 'date':
##    a string that describes the date of the data file,
##
##  - and the entries of the 'names' list;
##    each value is again a record whose component names are the identifiers
##    of the character tables of almost simple groups with socle the simple
##    group in question;
##    the value for each such identifier is a record whose component names
##    are '0' and the prime divisors of the group order,
##    with value a list that describes the irreducible characters of even
##    degree that have indicator +;
##    each entry is a list of the form '[ <name>, <pos>, <OD>, <source> ]',
##    where
##    <name> is a string that describes the character (degree and a
##    combination of letters that identifies the character),
##    <pos> is the position of the character in the list of irreducibles,
##    <OD> is a string that describes the orthogonal discriminant
##    ("?" for unknown, otherwise applying 'AtlasIrrationality' yields the
##    value as a GAP cyclotomic), and
##    <source> is a string that describes how the value was obtained.
##    
BindGlobal( "OD_data", JsonStringToGap( StringFile(
    Filename( OD_pkgdir, "data/odresults.json" ) ) ) );


##############################################################################
##
##  Read the functions.
##

Read( Filename( OD_pkgdir, "gap/oddata.g" ) );
Read( Filename( OD_pkgdir, "gap/fix.g" ) );
Read( Filename( OD_pkgdir, "gap/interface.g" ) );
Read( Filename( OD_pkgdir, "gap/consistency.g" ) );
if LoadPackage( "Browse", false ) = true then
  Read( Filename( OD_pkgdir, "gap/browse.g" ) );
fi;

