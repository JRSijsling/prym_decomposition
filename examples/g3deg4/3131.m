SetVerbose("FindCovs", 0);
SetSeed(1);

// Degree of map from X to E
degXE := 4;
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
typ1 := [<1,degXE>];
typ2 := [<2,degXE>];
typ3 := [<3,1>,<1,1>];
typ32 := [<3,2>,<1,2>];
/* Ramification over branch points */
comptyps := [ typ2, typ2, typ2, typ2, typ32 ];
mergtyps := [ [ typ1 ], [ typ1 ], [ typ1 ], [ typ1 ], [ typ3, typ3 ] ];

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
S4
Order:
24
Genus of Galois closure:
9

Number of different Prym data types:
1
Number of good non-hyperelliptic curves:
0
Number of bad non-hyperelliptic curves:
0
Number of good hyperelliptic curves:
0
Number of bad hyperelliptic curves:
27

----------------------------------------
Type 1

Z hyperelliptic from cover?
false
X hyperelliptic from cover?
true
Full Prym generated?
false
Genera for relevant subgroups:
[]

===== Group number 2 =====

Monodromy group:
C2*S4
Order:
48
Genus of Galois closure:
17

Number of different Prym data types:
2
Number of good non-hyperelliptic curves:
54
Number of bad non-hyperelliptic curves:
0
Number of good hyperelliptic curves:
36
Number of bad hyperelliptic curves:
0

----------------------------------------
Type 1

Z hyperelliptic from cover?
false
X hyperelliptic from cover?
true
Full Prym generated?
true
Genera for relevant subgroups:
[ [* 8, D4, 2 *], [* 8, D4, 2 *], [* 8, D4, 2 *] ]

----------------------------------------
Type 2

Z hyperelliptic from cover?
false
X hyperelliptic from cover?
false
Full Prym generated?
true
Genera for relevant subgroups:
[ [* 4, C2^2, 1 *], [* 4, C2^2, 1 *], [* 4, C2^2, 1 *], [* 4, C2^2, 2 *], [* 4, C2^2, 2 *], [* 4, C2^2, 2 *], [* 6, S3, 1 *], [* 6, S3, 1 *], [* 6, S3, 1 *], [* 6, S3, 1 *], [* 8, C2^3, 1 *], [* 8, C2^3, 1 *], [* 8, C2^3, 1 *], [* 8, D4, 1 *], [* 8, D4, 1 *], [* 8, D4, 1 *], [* 12, D6, 1 *], [* 12, D6, 1 *], [* 12, D6, 1 *], [* 12, D6, 1 *] ]

===== Group number 3 =====

Monodromy group:
C2^2:S4
Order:
96
Genus of Galois closure:
33

Number of different Prym data types:
1
Number of good non-hyperelliptic curves:
54
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
[ [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *], [* 6, S3, 2 *] ]
*/
