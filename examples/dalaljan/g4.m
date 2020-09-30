SetVerbose("FindCovs", 1);

// Degree of map from X to E
degXE := 2;
// Genus of X
gX := 8;
// Degree of map from E to PP^1
degEPP1 := 2;
// Genus of E
gE := 4;
// Bound on size of monodromy group
GBound := Infinity();
// Only study indecomposable maps?
Indec := false;
// Print full genera and rank sequences?
GenRank := true;

n := degEPP1*degXE;
/* Ramification types over single points of the base curve */
/* Format: < Index, number of points with that index > */
typ2 := [<2,1>, <1,n-2>];
typn := [<2,degXE>];
/* Ramification over branch points */
comptyps := [ typn, typn, typn, typn, typn, typn, typn, typn, typn, typn, typ2, typ2 ];
mergtyps := [ ];

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

    extcovs := CoversFromRamificationAndGenera(G, comptyps, dXgX, dEgE : Indec := Indec, MergTyps := mergtyps);
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

/*
===== Group number 1 =====

Monodromy group:
D4
Order:
8
Genus of Galois closure:
13

Number of different Prym data types:
1
Number of good non-hyperelliptic curves:
128
Number of bad non-hyperelliptic curves:
0
Number of good hyperelliptic curves:
0
Number of bad hyperelliptic curves:
0

----------------------------------------
Type 1

Z hyperelliptic from cover?
false
X hyperelliptic from cover?
false
Full Prym generated?
true
Genera for relevant subgroups:
[ [* 2, C2, 3 *], [* 2, C2, 3 *] ]
*/
