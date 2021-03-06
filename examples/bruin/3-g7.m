SetVerbose("FindCovs", 1);

// Degree of map from X to E
degXE := 2;
// Genus of X
gX := 7;
// Degree of map from E to PP^1
degEPP1 := 3;
// Genus of E
gE := 4;
// Bound on size of monodromy group
GBound := Infinity();
GBound := 24;
// Take ambient isomorphism when finding covers?
AmbIso := false;
// Only study indecomposable maps?
Indec := false;
// Only find genera of intermediate lattice (cheaper)?
OnlyGenera := true;
// Print full genera and rank sequences?
GenRank := true;
// Number of covers to sample
ncovs := 24;

n := degEPP1*degXE;
/* Ramification types over single points of the base curve */
/* Format: < Index, number of points with that index > */
typ2 := [ <2,2>, <1,2> ];
typ1 := [ [<1,2>], [<1,2>] ];
typ3 := [ <3,2> ];
typ0 := [ [<1,2>] ];
/* Ramification over branch points */
comptyps := [ typ2 : i in [1..10] ] cat [ typ3 ];
mergtyps := [ typ1 : i in [1..10] ] cat [ typ0 ];
comptyps := [ typ2 : i in [1..8] ] cat [ typ3 : j in [1..2] ];
mergtyps := [ typ1 : i in [1..8] ] cat [ typ0 : j in [1..2] ];
comptyps := [ typ2 : i in [1..6] ] cat [ typ3 : j in [1..3] ];
mergtyps := [ typ1 : i in [1..6] ] cat [ typ0 : j in [1..3] ];
comptyps := [ typ2 : i in [1..4] ] cat [ typ3 : j in [1..4] ];
mergtyps := [ typ1 : i in [1..4] ] cat [ typ0 : j in [1..4] ];
comptyps := [ typ2 : i in [1..2] ] cat [ typ3 : j in [1..5] ];
mergtyps := [ typ1 : i in [1..2] ] cat [ typ0 : j in [1..5] ];
comptyps := [ typ3 : j in [1..6] ];
mergtyps := [ typ0 : j in [1..6] ];
comptyps := [ typ2 : i in [1..12] ];
mergtyps := [ typ1 : i in [1..12] ];

dXgX := [ degXE, gX ];
dEgE := [ degEPP1, gE ];

S := SymmetricGroup(degEPP1*degXE);
Gs := [ rec`subgroup : rec in Subgroups(S) ];
Gs := [ G : G in Gs | #G le GBound ];
Gs := [ G : G in Gs | ExistsSequenceOfSubgroups(G, degXE, degEPP1 : Indec := Indec) ];
//Gs := [ Gs[6] ];

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
    extcovs := FilterPryms(extcovss[i]);
    PrintPrymData(extcovs : GenRank := true);
end for;


