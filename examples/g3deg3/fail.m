SetVerbose("FindCovs", 0);

// Degree of map from X to E
degXE := 3;
// Genus of X
gX := 3;
// Degree of map from E to PP^1
degEPP1 := 2;
// Genus of E
gE := 1;
// Bound on size of monodromy group
GBound := Infinity();
// Take ambient isomorphism when finding covers?
AmbIso := true;
// Only study indecomposable maps?
Indec := false;
// Only find genera of intermediate lattice (cheaper)?
OnlyGenera := false;
// Print full genera and rank sequences?
GenRank := true;

n := degEPP1*degXE;
/* Ramification types over single points of the base curve */
/* Format: < Index, number of points with that index > */
typ2 := [<2,degXE>];
typnew1 := [<3,1>,<2,1>,<1,1>];
typnew2 := [<2,1>,<1,4>];
comptyps := [ typ2, typ2, typ2, typ2, typnew1, typnew2 ];
typ1 := [[<1,degXE>]];
mtypnew1 := [[<3,1>],[<2,1>,<1,1>]];
mtypnew2 := [[<2,1>,<1,1>],[<1,3>]];
mergtyps := [ typ1, typ1, typ1, typ1, mtypnew1, mtypnew2 ];

//typ2 := [<2,degXE>];
//typnew1 := [<3,1>,<1,3>];
//typnew2 := [<2,2>,<1,2>];
//comptyps := [ typ2, typ2, typ2, typ2, typnew1, typnew2 ];
//typ1 := [[<1,degXE>]];
//mtypnew1 := [[<3,1>],[<1,3>]];
//mtypnew2 := [[<2,1>,<1,1>],[<2,1>,<1,1>]];
//mergtyps := [ typ1, typ1, typ1, typ1, mtypnew1, mtypnew2 ];

dXgX := [ degXE, gX ];
dEgE := [ degEPP1, gE ];

S := SymmetricGroup(degEPP1*degXE);
Gs := [ rec`subgroup : rec in Subgroups(S) ];
Gs := [ G : G in Gs | #G le GBound ];
Gs := [ G : G in Gs | ExistsSequenceOfSubgroups(G, degXE, degEPP1 : Indec := Indec) ];

extcovss := [ ];
for G in Gs do
    vprint FindCovs : "";
    vprint FindCovs : "===================================================";
    vprint FindCovs : "Checking monodromy group of order", #G;

    extcovs := CoversFromRamificationAndGenera(G, comptyps, dXgX, dEgE : AmbIso := AmbIso, Indec := Indec, MergTyps := mergtyps);
    vprint FindCovs : "";
    vprint FindCovs : "Number of admissible tuples:";
    vprint FindCovs : #extcovs;
    vprint FindCovs : "===================================================";
    if #extcovs ne 0 then
        Append(~extcovss, extcovs);
    end if;
end for;

print "";
print "Numbers of admissible tuples for groups yielding admissible covers:";
print [ #extcovs : extcovs in extcovss ];

for i:=1 to #extcovss do
    print "";
    print "===== Group number", i, "=====";
    extcovs := FilterPryms(extcovss[i] : OnlyGenera := OnlyGenera);
    PrintPrymData(extcovs : GenRank := GenRank, OnlyGenera := OnlyGenera);
end for;
