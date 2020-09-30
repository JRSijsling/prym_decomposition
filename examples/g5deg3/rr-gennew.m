SetVerbose("FindCovs", 0);

// Degree of map from X to E
degXE := 3;
// Genus of X
gX := 4;
// Degree of map from E to PP^1
degEPP1 := 3;
// Genus of E
gE := 1;
// Bound on size of monodromy group
GBound := Infinity();
// Take ambient isomorphism when finding covers?
AmbIso := false;
// Only study indecomposable maps?
Indec := false;
// Only find genera of intermediate lattice (cheaper)?
OnlyGenera := false;
// Print full genera and rank sequences?
GenRank := true;
// Number of covers to sample
ncovs := 48;

n := degEPP1*degXE;
/* Ramification types over single points of the base curve */
/* Format: < Index, number of points with that index > */
typ1 := [<2,3>,<1,3>];
typ2 := [<3,3>];
typnr := [<1,3>];
typtr := [<3,1>];
/* Ramification over branch points */
comptyps := [ typ1, typ1, typ1, typ1, typ1, typ1, typ2 ];
mergtyps := [ [typnr,typnr], [typnr,typnr], [typnr,typnr], [typnr,typnr], [typnr,typnr], [typnr,typnr], [typtr,typtr,typtr] ];

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

    extcovs := CoversFromRamificationAndGeneraSample(G, comptyps, dXgX, dEgE, ncovs : AmbIso := AmbIso, Indec := Indec, MergTyps := mergtyps);
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
