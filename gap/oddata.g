#############################################################################
##
##  functions for creating/updating the Json format data file with
##  'OD_load_source' and 'OD_write_data'
##


#############################################################################
##
#F  OD_NamesOfSimpleAtlasTables( <bound> )
##
##  Return the list of names of character tables of simple Atlas group,
##  ordered by group order, up to the upper bound given by <A>bound</A>,
##  where <A>bound</A> can be either an integer or the name of a
##  character table.
##
OD_NamesOfSimpleAtlasTables:= function( bound )
  if IsString( bound ) then
    bound:= Size( CharacterTable( bound ) );
  elif not IsInt( bound ) then
    Error( "<bound> must be an integer or the name of a character table" );
  fi;

  return AllCharacterTableNames(
           IsSimple, true,
           IsAbelian, false,
           IsDuplicateTable, false,
           Size, x -> x <= bound,
           InfoText, x -> PositionSublist( x,
                            "origin: ATLAS of finite groups" ) <> fail
           : OrderedBy:= Size );
end;

OD_simple_names:= OD_NamesOfSimpleAtlasTables( "Co2" );


# Compute the names of non-dashed automorphic extensions.
# (Note that "2F4(2)'" must be kept.)
OD_NamesOfAlmostSimpleAtlasTables:= function( simpname )
  return Filtered(
    CTblLib.DisplayAtlasMap_ComputePortions( simpname, 0 ).identifiers[1],
    x -> x = simpname or not EndsWith( x, "'" ) );
end;


#############################################################################
##
#F  OD_Data( <name> )
##
OD_Data:= function( name )
  local pos, simpname, data;

  pos:= Position( name, '.' );
  if pos = fail then
    simpname:= name;
  else
    simpname:= name{ [ 1 .. pos-1 ] };
  fi;

  if not IsBound( OD_data.( simpname ) ) then
    return fail;
  fi;
  data:= OD_data.( simpname );
  if not IsBound( data.( name ) ) then
    return fail;
  fi;
  return data.( name );
end;


#############################################################################
##
#F  OD_CharacterName( <t>, <i> )
##
##  Return the character name of the <i>-th character of the character table
##  <t>:
##  degree followed by the j-th word in terms of a..z if the character is the
##  j-th character of this degree in the table;
##  thus "6a" is the first character of degree 6,
##  "6b" is the second character of degree 6, etc.
##
OD_CharacterName:= function( t, i )
  local deg, n, j, alp;

  deg:= Irr( t )[i][1];
  n:= 0;
  for j in [ 1 .. i ] do
    if Irr( t )[j][1] = deg then
      n:= n + 1;
    fi;
  od;

  alp:= List( "abcdefghijklmnopqrstuvwxyz", x -> [ x ] );
  while n > Length( alp ) do
    Append( alp, List( alp, x -> Concatenation( "(", x, "')" ) ) );
  od;

  return Concatenation( String( deg ), alp[n] );
end;


#############################################################################
##
##  create the scaffold for the OD data of a given group,
##  using only the character tables (without entering values)
##
OD_scaffold_p:= function( ordt, p )
  local modt, ind, cand, showS;

  if p = 0 then
    modt:= ordt;
  else
    modt:= ordt mod p;
  fi;
  if modt = fail then
    return fail;
  fi;

  if p = 2 then
    ind:= ComputedIndicators( modt );
    if IsBound( ind[2] ) then
      ind:= ComputedIndicators( modt )[2];
    else
      # We cannot determine the list of irreducibles with indicator +.
      Info( InfoOD, 1,
            "no indicator stored for ", Identifier( modt ) );
      return [];
    fi;
  else
    ind:= Indicator( modt, Irr( modt ), 2 );
  fi;
  cand:= Filtered( [ 1 .. NrConjugacyClasses( modt ) ],
             i -> Irr( modt )[i][1] mod 2 = 0
                  and ind[i] = 1 );

  showS:= ( p = 2 and IsEvenInt( Number( Irr( ordt ), x -> x[1] = 1 ) ) );
  if showS then
    return List( cand, i -> [ OD_CharacterName( modt, i ), i, "?", "?", "" ] );
  else
    return List( cand, i -> [ OD_CharacterName( modt, i ), i, "?", "" ] );
  fi;
end;


OD_scaffold:= function( simpname )
  local names, result, name, t, p, res;

  names:= OD_NamesOfAlmostSimpleAtlasTables( simpname );

  result:= rec( names:= [] );
  for name in names do
    t:= CharacterTable( name );
    if t <> fail then
      Add( result.names, name );
      result.( name ):= rec();
      for p in Concatenation( [ 0 ], PrimeDivisors( Size( t ) ) ) do
        res:= OD_scaffold_p( t, p );
        if res = fail then
          Info( InfoOD, 2,
                "no data for ", simpname, ", p = ", p, "\n" );
        else
          result.( name ).( p ):= res;
        fi;
      od;
    fi;
  od;

  return result;
end;

# create all scaffolds we need
OD_initial_data:= function()
  local result, simpname;

  result:= rec( names:= [] );
  for simpname in OD_simple_names do
    Add( result.names, simpname );
    result.( simpname ):= OD_scaffold( simpname );
  od;

  return result;
end;


#############################################################################
##
##  Translate 'odresults.odt' to plain text (without writing to a file).
##
OD_contents_odt:= function( name_odresults_odt... )
    local srcfile_odt, prg, str, out, res;

    if Length( name_odresults_odt ) = 0 then
      srcfile_odt:= Filename( OD_pkgdir, "data/odresults.odt" );
    else
      srcfile_odt:= name_odresults_odt[1];
    fi;

    prg:= Filename( DirectoriesSystemPrograms(), "libreoffice" );
    if prg = fail then
      Error( "no 'libreoffice' available" );
    fi;
    str:= "";;
    out:= OutputTextString( str, true );;
    res:= Process( DirectoryCurrent(), prg, InputTextUser(), out,
                   ["--cat", srcfile_odt ] );
    if res <> 0 then
      Error( "translation of ", srcfile_odt, " failed" );
    fi;
    CloseStream( out );

    return str;
end;


##  extract the date from string of the current '.odt' file
OD_source_date:= function( str )
    local pos, i;

    pos:= PositionNthOccurrence( str, '\n', 2 );
    i:= pos-1;
    while str[i] <> ' ' do
      i:= i-1;
    od;
    return str{ [ i+1 .. pos-1 ] };
end;


#############################################################################
##
##  extract the values stored in 'odresults.odt';
##  <str> is assumed to be a string obtained by converting this file
##  to text format
##
OD_distribute_txt_to_groups:= function( str )
    local pos, lines, linespergroup, start, i;

    # Cut off the introductory text.
    pos:= PositionSublist( str,
              "Only cyclic outer automorphism groups are considered." );
    pos:= Position( str, '\n', pos );
    str:= str{ [ pos+1 .. Length( str ) ] };

    # Replace tabs.
    lines:= List( SplitString( str, "\n" ), NormalizedWhitespace );

    # Omit empty lines and lines starting with "Deg" or "G Deg".
    lines:= Filtered( lines, x -> x <> "" and
                                  not StartsWith( x, "Deg" ) and
                                  not StartsWith( x, "G Deg" ) );

    # Find those lines that are identifiers of simple Atlas groups,
    # and assign the following lines to these groups.
    linespergroup:= [];
    start:= 0;
    for i in [ 1 .. Length( lines ) ] do
      if lines[i] in OD_simple_names then
        if start <> 0 then
          Add( linespergroup, lines{ [ start .. i-1 ] } );
        fi;
        start:= i;
      fi;
    od;
    Add( linespergroup, lines{ [ start .. Length( lines ) ] } );

    return linespergroup;
end;


#############################################################################

OD_set_entries:= function( simpname, name, p, entries, origin, data )
    local t, tdegs, tnames, names, digitparts, tdegs_collect,
          digitparts_collect, values, pairs, currdegree, i, charname, value,
          degree, currpos, pos, entry, set1, set2;

    data:= data.( simpname ).( name ).( p );
    t:= CharacterTable( name );
    if p <> 0 then
      t:= t mod p;
    fi;
    tdegs:= List( Irr( t ){ List( data, l -> l[2] ) }, x -> x[1] );
    tnames:= List( data, l -> l[1] );

    names:= entries{ [ 1, 3 .. Length( entries ) - 1 ] };
    digitparts:= List( names, x -> Int( Filtered( x, IsDigitChar ) ) );

    # consistency check:
    # Do the character degrees in the file occur enough often
    # in the character table?
    tdegs_collect:= Collected( tdegs );
    digitparts_collect:= Collected( digitparts );
    if ForAny( digitparts_collect,
               pair -> not pair[1] in tdegs or
                           First( tdegs_collect,
                                  pair2 -> pair2[1] = pair[1] )[2] < pair[2] ) then
      Print( "#E  ", simpname, ", p = ", p, ": degrees do not fit;\n",
             "#E  expected from character table:\n",
             "#E  ", tnames, "\n",
             "#E  found in file:\n",
             "#E  ", names, "\n" );
      return;
    fi;

    values:= entries{ [ 2, 4 .. Length( entries ) ] };
    pairs:= List( [ 1 .. Length( names ) ], i -> [ names[i], values[i] ] );
    StableSortParallel( digitparts, pairs );

    currdegree:= 0;
    for i in [ 1 .. Length( names ) ] do
      value:= pairs[i][2];
      charname:= pairs[i][1];
      Info( InfoOD, 2,
            "i = ", i, ", deal with ", [ value, charname ], "\n" );
      if charname in tnames then
        # The degree plus the position string are given.
        pos:= Position( tnames, charname );
      else
        # Find the right position.
        degree:= digitparts[i];
        if degree <> currdegree then
          currpos:= 1;
          currdegree:= degree;
        else
          currpos:= currpos + 1;
        fi;
        # Thus we have the 'currpos'-th character of degree 'degree' in 't'.
        pos:= PositionNthOccurrence( tdegs, degree, currpos );
      fi;
      entry:= data[ pos ];
      set1:= fail;
      set2:= fail;

      if 'S' in value and p <> 2 then
        Info( InfoOD, 2,
              "unknown value ", value, " for p = ", p, "\n" );
      elif p = 0 then
        value:= ReplacedString( value, "−", "-" );
        if value = "???" or value = "??" then
          set1:= "?";
        else
          set1:= value;
        fi;
      elif value = "O+" then
        set1:= "O+";
      elif value = "O−" then
        set1:= "O-";
      elif value = "O−S−" then
        set1:= "O-";
        set2:= "S-";
      elif value = "O+S+" then
        set1:= "O+";
        set2:= "S+";
      elif value = "O+S−" then
        set1:= "O+";
        set2:= "S-";
      elif value = "S+" then
        set1:= "?";
        set2:= "S+";
      elif value = "S−" then
        set1:= "?";
        set2:= "S-";
      elif value = "???" or value = "??" then
        set1:= "?";
        if p = 2 then
          set2:= "?";
        fi;
      else
        Info( InfoOD, 2,
              "unknown value ", value, " for p = ", p, "\n" );
      fi;
      # set the value
      if entry[3] = "?" then
        entry[3]:= set1;
      elif entry[3] <> set1 then
        Error( "#E1  try to replace '", entry[3], "' by '", set1, "'\n" );
        entry[3]:= set1;
      fi;
      if set2 <> fail then
        if entry[4] = "?" then
          entry[4]:= set2;
        elif entry[4] <> set2 then
          Error( "#E2  try to replace '", entry[4], "' by '", set2, "'\n" );
          entry[4]:= set2;
        fi;
      fi;

      # set the comment if there is something to say
      if entry[ Length( entry ) ] = "" then
        if set1 <> "?" or ( set2 <> fail and set2 <> "?" ) then
          entry[ Length( entry ) ]:= origin;
        fi;
      elif entry[ Length( entry ) ] <> origin then
        Error( "#E3  try to replace '", entry[ Length( entry ) ], "' by '", origin, "'\n" );
      fi;
    od;
end;


#############################################################################
##
##  create 'OD_data' anew from the file 'odresults.odt'
##
OD_load_source:= function( name_odresults_odt... )
    local contents, OD_data_new, linespergroup, curr_origin, bunch, simpname,
          Gdata, datap, bracketisopen, line, bracketpos, comment, p, spl,
          entries, i, name;

    contents:= CallFuncList( OD_contents_odt, name_odresults_odt );

    # reset 'OD_data'.
    OD_data_new:= OD_initial_data();

    # set the date stored in the file
    OD_data_new.date:= OD_source_date( contents );

    linespergroup:= OD_distribute_txt_to_groups( contents );;

    # who has provided the data coming next
    curr_origin:= "";

    for bunch in linespergroup do
      simpname:= bunch[1];
      Info( InfoOD, 2,
            "deal with group ", simpname );
      Gdata:= OD_data_new.( simpname );
      datap:= "";
      bracketisopen:= false;
      for line in Concatenation( bunch{ [ 2 .. Length( bunch ) ] },
                                 [ "Mod" ] ) do
        if StartsWith( line, "<" ) then
          # the line is expected to have the form "<RP>" or so
          curr_origin:= line{[2 .. Length(line)-1]};
        else
          bracketpos:= Position( line, '[' );
          if bracketpos <> fail then
            # ignore comments of the form "[...]" in the source file
            comment:= line{ [ bracketpos .. Length( line ) ] };
            Info( InfoOD, 2,
                  "comment in line: ", comment );
            line:= line{ [ 1 .. bracketpos-1 ] };
            if not ']' in comment then
              # comments may contain line breaks
              bracketisopen:= true;
            fi;
          fi;
          if bracketisopen and line in bunch then
            bracketpos:= Position( line, ']' );
            if bracketpos <> fail then
              Info( InfoOD, 2,
                    "continued in line: ", line );
              bracketisopen:= false;
            fi;
          elif StartsWith( line, "Ordinary" ) then
            # assumed that this comes before "Mod" lines for the group
            p:= 0;
            datap:= "";
          elif StartsWith( line, "Mod" ) then
            if datap <> "" then
              # deal with the previous p:
              datap:= NormalizedWhitespace( datap );
              if not StartsWith( datap, "G " ) then
                Info( InfoOD, 2,
                      "insert initial 'G'" );
                datap:= Concatenation( "G ", datap );
              fi;
              spl:= SplitString( datap, " " );
              entries:= rec();
              for i in [ 1 .. Length( spl ) ] do
                if StartsWith( spl[i], "G" ) then
                  if spl[i] = "G.21" then
                    name:= Concatenation( simpname, ".2_1" );
                  elif spl[i] = "G.22" then
                    name:= Concatenation( simpname, ".2_2" );
                  elif spl[i] = "G.23" then
                    name:= Concatenation( simpname, ".2_3" );
                  else
                    name:= Concatenation( simpname,
                               spl[i]{ [ 2 .. Length( spl[i] ) ] } );
                  fi;
                  if not name in RecNames( Gdata ) then
                    Error( "problem with group ", spl[i], "?\n" );
                  fi;
                  entries.( name ):= [];
                else
                  Add( entries.( name ), spl[i] );
                fi;
              od;
              for name in RecNames( entries ) do
                if entries.( name ) <> [ "None" ] then
                  OD_set_entries( simpname, name, p, entries.( name ),
                                  curr_origin, OD_data_new );
                fi;
              od;
            fi;
            p:= Int( Filtered( line, IsDigitChar ) );
            datap:= "";
          elif line <> "" then
            # data for the given p
            Append( datap, " " );
            Append( datap, line );
          fi;
        fi;
      od;
    od;

    # finally, replace the contents of 'OD_data'
    MakeReadWriteGlobal( "OD_data" );
    UnbindGlobal( "OD_data" );
    BindGlobal( "OD_data", OD_data_new );
end;


#############################################################################
##
#F  OD_enter_value( <name>, <p>, <charnr>, <val>, <origin>[, <mode>] )
##
##  Change 'OD_data' such that the entry given by the arguments gets set;
##  <origin> gets appended to the origin string of the entry if this
##  information is new.
##
##  <val> must be a *string* that describes the OD in question.
##
##  If <mode> is given then it determines how to handle inconsistencies,
##  that is, an attempt to replace a known value by a different one.
##  Supported values are
##
##  - "error":
##    signal an error in case of an inconsistency
##    (before changing the value in question)
##
##  - "test":
##    do not change any value,
##    do not signal errors,
##    print messages about inconsistencies
##
##  - "replace":
##    change all values without signaling an error
##
##  The default for <mode> is "error".
##
OD_enter_value:= function( name, p, charnr, val, origin, mode... )
    local pos, simpname, data, entry, F;

    pos:= Position( name, '.' );
    if pos = fail then
      simpname:= name;
    else
      simpname:= name{ [ 1 .. pos-1 ] };
    fi;

    if Length( mode ) = 0 then
      mode:= "error";
    elif mode[1] in [ "error", "replace", "test" ] then
      mode:= mode[1];
    else
      Error( "<mode> must be one of \"error\", \"replace\", \"test\"" );
    fi;

    if not IsBound( OD_data.( simpname ) ) then
      Info( InfoOD, 1,
            "cannot store info about group '", simpname, "'" );
      return false;
    fi;
    data:= OD_data.( simpname );
    if not IsBound( data.( name ) ) then
      Info( InfoOD, 1,
            "cannot store info about group '", name, "'" );
      return false;
    fi;
    data:= data.( name );
    if not IsBound( data.( p ) ) then
      Info( InfoOD, 1,
            "cannot store info about prime '", p, "'" );
      return false;
    fi;
    data:= data.( p );
    entry:= First( data, l -> l[2] = charnr );
    if entry = fail then
      Info( InfoOD, 1,
            "cannot store info about character '", pos, "'" );
      return false;
    fi;
    if entry[3] <> "?" then
      # Do we want to replace a known value by another one?
      if p > 0 then
        if entry[3] <> val then
          # The two values are incompatible.
          Info( InfoOD, 1,
                "replace value for '", name, "', p = ", p, ", char. ", charnr,
                ": '", entry[3], "' -> '", val, "'" );
          if mode = "error" then
            Error( "inconsistency" );
          fi;
        fi;
      elif AtlasIrrationality( entry[3] ) <> AtlasIrrationality( val ) then
        # Perhaps the two values are in the same square class.
        F:= CharacterField( Irr( CharacterTable( name ) )[ charnr ] );
        if SquareRootInNumberField( F, AtlasIrrationality( entry[3] )
               * AtlasIrrationality( val ) ) = fail then
          # The two values are incompatible.
          Info( InfoOD, 1,
                "replace value for '", name, "', p = ", p, ", char. ", charnr,
                ": '", entry[3], "' -> '", val, "', w.r.t. ", F );
          if mode = "error" then
            Error( "inconsistency" );
          fi;
        else
          # Take the "nicer" string description, in the sense that
          # it has a shorter string representation.
          if Length( entry[3] ) <= Length( val ) then
            val:= entry[3];
          fi;
        fi;
      fi;
    fi;
    if mode <> "test" then
      entry[3]:= val;
      pos:= Length( entry );
      if PositionSublist( entry[ pos ], origin ) = fail then
        if entry[ pos ] = "" then
          entry[ pos ]:= origin;
        else
          entry[ pos ]:= Concatenation( entry[ pos ], ",", origin );
        fi;
      fi;
    fi;

    return true;
end;


#############################################################################
##
#F  OD_enter_values( <list>, <mode> )
##
##  Change 'OD_data' such that the entries in <list> get entered.
##  Each entry is assumed to have the form '[ name, p, pos, val, origin ]'.
##
##  <mode> decides what happens in the case of an inconsistency.
##
OD_enter_values:= function( list, mode )
    local entry, res;

    for entry in list do
      if Length( entry ) <> 5 then
        Error( entry );
      fi;
      res:= CallFuncList( OD_enter_value, Concatenation( entry, [ mode ] ) );
      if res = false then
        Error( "OD_enter_value returned false" );
      fi;
    od;
end;


#############################################################################
##
#F  OD_string_data()
##
##  Return a Json format string describing the current contents of 'OD_data'.
##
OD_string_data:= function()
  local result, line, simpname, nams, name, p, cand, l;

  result:= "{\n\"date\":\"";

  Append( result, OD_data.date );
  Append( result, "\"," );

  Append( result, "\n\"comment\":[" );
  for line in OD_data.comment do
    Append( result, "\n \"" );
    Append( result, line );
    Append( result, "\"," );
  od;
  Unbind( result[ Length( result ) ] );
  Append( result, "\n]," );

  Append( result, "\n\"names\":" );
  Append( result, Concatenation( "[\"",
                      JoinStringsWithSeparator( OD_data.names, "\",\"" ),
                      "\"]," ) );

  for simpname in OD_data.names do
    Append( result, "\n\"" );
    Append( result, simpname );
    Append( result, "\":{" );
    if IsBound( OD_data.( simpname ).names ) then
      nams:= OD_data.( simpname ).names;
    else
      nams:= OD_NamesOfAlmostSimpleAtlasTables( simpname );
    fi;
    Append( result, "\n \"names\":[\"" );
    Append( result, JoinStringsWithSeparator( nams, "\",\"" ) );
    Append( result, "\"]," );
    for name in nams do
      Append( result, "\n \"" );
      Append( result, name );
      Append( result, "\":{" );
      for p in Set( RecNames( OD_data.( simpname ).( name ) ), Int ) do
        Append( result, "\n  \"" );
        Append( result, String( p ) );
        Append( result, "\":[" );
        cand:= OD_data.( simpname ).( name ).( p );
        for l in cand do
          Append( result, "\n   [\"" );
          Append( result, l[1] );
          Append( result, "\"," );
          Append( result, String( l[2] ) );
          Append( result, ",\"" );
          Append( result, String( l[3] ) );
          Append( result, "\",\"" );
          Append( result, String( l[4] ) );
          if Length( l ) = 5 then
            # characteristic 2
            Append( result, "\",\"" );
            Append( result, String( l[5] ) );
          fi;
          Append( result, "\"]," );
        od;
        if Length( cand ) <> 0 then
          Unbind( result[ Length( result ) ] );
        fi;
        Append( result, "]," );
      od;
      Unbind( result[ Length( result ) ] );
      Append( result, "}," );
    od;
    Unbind( result[ Length( result ) ] );
    Append( result, "}," );
  od;
  Unbind( result[ Length( result ) ] );
  Append( result, "}\n" );

  return result;
end;


#############################################################################
##
##  write the Json format string to a file
##
OD_write_data:= filename -> FileString( filename, OD_string_data() );

