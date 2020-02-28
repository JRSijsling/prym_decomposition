SetVerbose("FindCovs", 0);

// Degree of map from X to E
degXE := 2;
// Genus of X
gX := 2;
// Degree of map from E to PP^1
degEPP1 := 2;
// Genus of E
gE := 1;
// Bound on size of monodromy group
GBound := Infinity();
// Take ambient isomorphism when finding covers?
AmbIso := true;
// Only study indecomposable maps?
Indec := true;
// Only find genera of intermediate lattice (cheaper)?
OnlyGenera := true;
// Print full genera and rank sequences?
GenRank := true;

/* Ramification types over single points of the base curve */
/* Format: < Index, number of points with that index > */
typ2 := [<2,2>];
typ1 := [<2,degXE>];
comptyps := [ typ1, typ1, typ1, typ1, typ2 ];
typ2 := [<2,1>];
typ1 := [<1,degXE>];
mergtyps := [ [ typ1 ], [ typ1 ], [ typ1 ], [ typ1 ], [ typ2, typ2 ] ];

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

