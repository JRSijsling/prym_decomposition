SetVerbose("FindCovs", 0);

/* All covers are assumed to have a genus-0 target! */

S := SymmetricGroup(8);
cov := [
S ! (1, 7)(2, 8)(3, 6)(4, 5),
S ! (1, 7)(2, 8)(3, 5)(4, 6),
S ! (1, 7)(2, 4)(3, 6)(5, 8),
S ! (1, 8)(2, 7)(3, 6)(4, 5),
S ! (1, 6, 5, 2)(3, 4, 8, 7)
];
G := sub< S | cov >;

facs := ChevalleyWeilDecomposition(cov, G);
chartab := G`chartab;

print "";
print "Indices in the character table, multiplicities and degrees of corresponding representations:";
print facs;
print "";
print "G-module corresponding to first entry:";
print GModule(chartab[facs[#facs][1]][1]);

Hs := [ rec`subgroup : rec in Subgroups(G) ];
HX := Hs[17];
HY := Hs[21];

print "";
print "Group HX:";
print HX;
print "Group HY:";
print HY;

rk, gX, gY := PrymOperatorRank(cov, G, HX, HY);
print "";
print "Genus of X:", gX;
print "Genus of Y:", gY;
print "Dimension of image of Jac (X) --> Jac (Y):", rk;

