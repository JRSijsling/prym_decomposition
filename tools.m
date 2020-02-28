declare attributes GrpPerm : chartab, dctab;

intrinsic ExistsSequenceOfSubgroups(G::Grp, degXE::RngIntElt, degEPP1::RngIntElt : Indec := false) -> .
{Given a group G and degrees degXE and degEPP1, find subgroups of G up to conjugation in Sym (n) that yield corresponding covers.}

/* G has to be transitive */
if not IsTransitive(G) then return false, [ ]; end if;
/* HX is the stabilizer of 1, which is well-defined once G is given as a subgroup of S_n */
/* This is allowed because we at first take the groups G up to conjugacy in S_n, not up to a larger notion */
HX := Stabilizer(G, 1);
if not #Core(G, HX) eq 1 then return false, [ ]; end if;
test := #NormalSubgroups(HX : IndexLimit := Factorial(degXE - 1)) ne 0;
if not test then return false, [ ]; end if;

/* Take subgroups of correct index corresponding to degree of map E --> PP^1 */
HEs := [ rec`subgroup : rec in Subgroups(G : IndexEqual := degEPP1) ];
/* Merge all up to conjugacy in Sym (n) */
S := SymmetricGroup(Degree(G)); NG := Normalizer(S, G);
function compS(H1, H2); return IsConjugate(NG, H1, H2); end function;
HEs := ListUpToEquivalence(HEs, compS);

/* Now we find inclusions HX < HE < G by suitably conjugating HE */
NX := Normalizer(NG, HX);
subtups := [ ];
for HE in HEs do
    NE := Normalizer(NG, HE);
    reps := DoubleCosetRepresentatives(NG, NE, NX);
    HEsnew := [ HE^rep : rep in reps ];
    HEsnew := [ HEnew : HEnew in HEsnew | HX meet HEnew eq HX ];
    if Indec then
        HEsnew := [ HEnew : HEnew in HEsnew | IsMaximal(HEnew, HX) ];
    end if;
    subtups cat:= [ [ HEnew, HX ] : HEnew in HEsnew ];
end for;
return #subtups ne 0, subtups;

end intrinsic;


intrinsic MonodromyAndGenusIfBaseRational(extcov::List, H::Grp) -> .
{Given an extended cover extcov and a subgroup H of the corresponding monodromy group, returns the monodromy of Z/H --> PP1, as well as the genus. The latter is only correct when the base has genus 0.}

monG, G := Explode(extcov);
rhoH := CosetAction(G, H); monH := [ rhoH(sigma) : sigma in monG ];
d := Degree(Parent(monH[1]));
hH := -2*d + &+[ &+[ e[2]*(e[1] - 1) : e in CycleStructure(sigma) ] : sigma in monH ];
assert (hH + 2) mod 2 eq 0;
return monH, (hH + 2) div 2;

end intrinsic;


function TestCorrectGenera(extcov, gEgX)
/* Given a cover covG for the group G, along with the subgroups HE, HX
 * in subtups, checks equality of the resulting genera for E and X */

monG, G, HE, HX := Explode(extcov); gE, gX := Explode(gEgX);
monE, gEnew := MonodromyAndGenusIfBaseRational(extcov, HE);
if gEnew ne gE then return false; end if;
monX, gXnew := MonodromyAndGenusIfBaseRational(extcov, HX);
if gXnew ne gX then return false; end if;
return true;

end function;


intrinsic CoversFromRamificationAndGenera(G::Grp, typs::SeqEnum, dXgX::SeqEnum, dEgE::SeqEnum : AmbIso := true, Indec := false, MergTyps := [ ]) -> .
{Uses CoversFromRamification for the group G (up to ambient isomorphism if so desired). Degrees and genera are specified in the remaining arguments. We assume the base to be of genus 0 throughout.}

MergTyps := [ Set(m) : m in MergTyps ];
/* Note: We are free to play with S_n-conjugation everywhere as the relevant
 * ramification data and genera do not change */
dX, gX := Explode(dXgX); dE, gE := Explode(dEgE);
vprint FindCovs, 2 : "";
vprint FindCovs, 2 : "Finding sequences of subgroups...";
test, subtups := ExistsSequenceOfSubgroups(G, dX, dE);
vprint FindCovs, 2 : "done.";
if not test then return [ ]; end if;

/* Base has genus 0 throughout our considerations */
vprint FindCovs : "";
vprint FindCovs : "Number of covers:";
monGs := CoversFromRamification(G, 0, typs : AmbIso := AmbIso);
vprint FindCovs : #monGs;
if #monGs eq 0 then return [ ]; end if;

extcovs := [ ];
for monG in monGs do
    extcovsnew := [ ];
    /* Check which pairs H_X < H_E match to covG and give good genera */
    for subtup in subtups do
        HE, HX := Explode(subtup);
        extcov := [* monG, G, HE, HX *];
        if not TestCorrectGenera(extcov, [ gE, gX ]) then continue; end if;
        if #MergTyps ne 0 and (MergTyps ne IntermediateRamificationData(extcov, HX, HE)) then continue; end if;
        Append(~extcovsnew, [* monG, G, HE, HX *]);
    end for;
    extcovs cat:= extcovsnew;

    /* Superfluous assertions
    for extcov in extcovsnew do
        _, G, HE, HX := Explode(extcov);
        monE, gEnew := MonodromyAndGenusIfBaseRational(extcov, HE);
        monX, gXnew := MonodromyAndGenusIfBaseRational(extcov, HX);
        assert G meet HE eq HE;
        assert G meet HX eq HX;
        assert HE meet HX eq HX;
        assert #Core(G, HX) eq 1;
        assert gEnew eq gE;
        assert gXnew eq gX;
        for i:=1 to #typs do assert CycleStructure(monX[i]) eq typs[i]; end for;
    end for;
    */
end for;
return extcovs;

end intrinsic;


intrinsic CoversFromRamificationAndGeneraSample(G::Grp, typs::SeqEnum, dXgX::SeqEnum, dEgE::SeqEnum, ncovs::RngIntElt : AmbIso := true, Indec := false, MergTyps := [ ]) -> .
{Uses CoversFromRamification for the group G (up to ambient isomorphism if so desired). Degrees and genera are specified in the remaining arguments. We assume the base to be of genus 0 throughout.}

MergTyps := [ Set(m) : m in MergTyps ];
/* Note: We are free to play with S_n-conjugation everywhere as the relevant
 * ramification data and genera do not change */
dX, gX := Explode(dXgX); dE, gE := Explode(dEgE);
vprint FindCovs, 2 : "";
vprint FindCovs, 2 : "Finding sequences of subgroups...";
test, subtups := ExistsSequenceOfSubgroups(G, dX, dE);
//vprint FindCovs, 2 : #subtups;
vprint FindCovs, 2 : "done.";
if not test then return [ ]; end if;

/* Base has genus 0 throughout our considerations */
vprint FindCovs : "";
vprint FindCovs : "Number of covers:";
monGs := CoversFromRamificationSample(G, 0, typs, ncovs : AmbIso := AmbIso);
vprint FindCovs : #monGs;
if #monGs eq 0 then return [ ]; end if;

extcovs := [ ];
for monG in monGs do
    extcovsnew := [ ];
    /* Check which pairs H_X < H_E match to covG and give good genera */
    for subtup in subtups do
        HE, HX := Explode(subtup);
        extcov := [* monG, G, HE, HX *];
        if not TestCorrectGenera(extcov, [ gE, gX ]) then continue; end if;
        if #MergTyps ne 0 and (MergTyps ne IntermediateRamificationData(extcov, HX, HE)) then continue; end if;
        Append(~extcovsnew, [* monG, G, HE, HX *]);
    end for;
    extcovs cat:= extcovsnew;

    /* Superfluous assertions
    for extcov in extcovsnew do
        _, G, HE, HX := Explode(extcov);
        monE, gEnew := MonodromyAndGenusIfBaseRational(extcov, HE);
        monX, gXnew := MonodromyAndGenusIfBaseRational(extcov, HX);
        assert G meet HE eq HE;
        assert G meet HX eq HX;
        assert HE meet HX eq HX;
        assert #Core(G, HX) eq 1;
        assert gEnew eq gE;
        assert gXnew eq gX;
        for i:=1 to #typs do assert CycleStructure(monX[i]) eq typs[i]; end for;
    end for;
    */
end for;
return extcovs;

end intrinsic;


intrinsic AutomorphismsFromCover(extcov::List, H::Grp) -> .
{Finds automorphisms induced from the Galois closure.}

monG, G, HE, HX := Explode(extcov); assert H meet G eq H;
NH := Normalizer(G, H);
Q := quo< NH | H >;
return GroupName(Q);

end intrinsic;


intrinsic IsHyperellipticFromCover(extcov::List, H::Grp) -> .
{Checks if the quotient Z/H has a hyperelliptic quotient induced by elements of the monodromy group G.}

monG, G, HE, HX := Explode(extcov); assert H meet G eq H;
Jlist := [ J : J in MinimalOvergroups(G, H) | Index(J, H) eq 2 ];
for J in Jlist do
    monJ, gJ := MonodromyAndGenusIfBaseRational(extcov, J);
    if gJ eq 0 then return true, J; end if;
end for;
return false, [ ];

end intrinsic;


intrinsic ExtendedCoverData(extcov::List, H::Grp) -> .
{Returns the ramification structure of Z/H --> PP1 as a list [<ram index, number of ram points>], followed by the genus, the automorphism group, and a boolean indicating whether or not Z/H is hyperelliptic from the diagram of covers.}

monG, G, HE, HX := Explode(extcov); assert H meet G eq H;
monH, gH := MonodromyAndGenusIfBaseRational(extcov, H);
ramH := [ CycleStructure(sigma) : sigma in monH ];
A := AutomorphismsFromCover(extcov, H);
test := IsHyperellipticFromCover(extcov, H);
return ramH, gH, A, test;

end intrinsic;


intrinsic PrintExtendedCoverData(extcov::List, H::Grp)
{Prints the ramification structure of Z/H --> PP1 as a list [<ram index, number of ram points>], followed by the genus, the automorphism group, and a boolean indicating whether or not Z/H is hyperelliptic from the diagram of covers.}

ramH, gH, A, test := ExtendedCoverData(extcov, H);
print "";
print "Ramification:";
print ramH;
print "";
print "Genus of Z/H:";
print gH;
print "";
print "Automorphisms from cover group:";
print A;
print "";
print "Is Z/H hyperelliptic from the cover group?";
print test;

end intrinsic;


intrinsic IntermediateRamificationData(extcov::List, H1::Grp, H2::Grp) -> .
{Returns the ramification structure over each branched point of Z/H1 --> Z/H2 in the form of a list [<ramification index, # ram points>]. Merged points lead to multiple lists.}

monG, G, HE, HX := Explode(extcov);
assert H1 meet G eq H1; assert H2 meet G eq H2;

sigmaints := [ ];
for sigma in monG do
    reps := DoubleCosetRepresentatives(G, sub< G | sigma >, H2);
    sigmaint := [ ];
    for rep in reps do
        /* Conjugate is rep^(-1)*sigma*rep */
        sigmacon := sigma^rep;
        e := Minimum([ i : i in [1..Order(sigma)] | sigmacon^i in H2 ]);
        Append(~sigmaint, H2 ! (sigmacon^e));
    end for;
    Append(~sigmaints, sigmaint);
end for;

rho := CosetAction(H2, H1);
return [ { CycleStructure(rho(sigma)) : sigma in sigmaint } : sigmaint in sigmaints ];

end intrinsic;


intrinsic PrintIntermediateRamificationData(extcov::List, H1::Grp, H2::Grp)
{Prints the ramification structure over each branched point of Z/H1 --> Z/H2 in the form of a list [<ramification index, # ram points>]. Merged points lead to multiple lists.}

data := IntermediateRamificationData(extcov, H1, H2);
print data;

end intrinsic;


intrinsic PrintExtendedCoverData(extcov::List : Lattice := false)
{Describes the full lattice of covers for the extended cover extcov.}

monG, G, HE, HX := Explode(extcov);

print "";
print "===== Data for monodromy group =====";
print "";
print "Order:";
print #G;
print "";
print "Name:";
print GroupName(G);

print "";
print "===== Data for X/PP1 =====";
PrintExtendedCoverData(extcov, HX);

print "";
print "===== Data for E/PP1 =====";
PrintExtendedCoverData(extcov, HE);

print "";
print "===== Ramification of X --> E =====";
PrintIntermediateRamificationData(extcov, HX, HE);

if Lattice then
    print "";
    print "===== Quotient lattice =====";
    Hs := [ rec`subgroup : rec in Subgroups(G) ];
    for H in Hs do
        print "";
        print "----------------------------------------";
        print "Size of subgroup H:";
        print #H;
        print "Name of subgroup H:";
        print GroupName(H);
        PrintExtendedCoverData(extcov, H);
    end for;
end if;

end intrinsic;


intrinsic ChevalleyWeilDecomposition(monG::SeqEnum, G::Grp) -> .
{Using Chevalley-Weil, compute the multiplicity of the irreducible G-representations to the elements of the character table chartab in H^0(Z, omega^1). Here Z is the curve coming from the monodromy monG.}

/* Initialize extended character table */
if assigned G`chartab then
    chartab := G`chartab;
else
    chartab := CharacterTable(G);
    chartab := [ [* char *] : char in chartab ];
    G`chartab := chartab;
end if;

facs := [ ];
for charind in [1..#chartab] do
    char := chartab[charind][1];

    /* Next line assumes gX = 0 */
    mult := -Degree(char);
    for sigma in monG do
        e := Order(sigma);
        if not e gt 1 then continue; end if;

        /* TODO: The following approach could be more elegant. But it works. */
        vprint FindCovs, 3 : "Calculating multiplicity...";
        deg := Degree(char);
        TracesPowers := [ char(sigma^i) : i in [1..deg] ];
        p := PowerSumsToPolynomial(TracesPowers);

        K := BaseRing(Parent(p));
        Cy<zeta> := CyclotomicField(e);
        K2 := Compositum(K, Cy);
        P<x> := PolynomialRing(K2);

        z := K2! zeta;
        Nmua := [ Rationals() ! Valuation(P!p, x - z^a) : a in [1..e-1] ];
        mult +:= &+[ Nmua[a]*FractionalPart(-a/e) : a in [1..e-1] ] ;
        vprint FindCovs, 3 : "done.";
    end for;

    mult := Integers() ! mult;
    /* Trivial representation gets one more */
    if char eq 1 then mult +:= 1; end if;
    if mult ne 0 then Append(~facs, [* charind, mult, deg *]); end if;
end for;
return facs;

end intrinsic;


function ImagesOfProjection(facs, G, H1, H2, chartab)

ims := [ ];
for fac in facs do
    charind, mult := Explode(fac);
    /* Update character table */
    if #chartab[charind] eq 1 then
        vprint FindCovs, 3 : "Determining G-module...";
        M := GModule(chartab[charind][1]);
        phi := GModuleAction(M);
        vprint FindCovs, 3 : "done.";
        Append(~chartab[charind], phi);
        Append(~chartab[charind], AssociativeArray());
        Append(~chartab[charind], AssociativeArray());
    end if;

    found, im := IsDefined(chartab[charind][3], [ H1, H2 ]);
    if not found then
        phi := chartab[charind][2];
        vprint FindCovs, 3 : "Determining maps...";

        /* Update operator list */
        found1, t1 := IsDefined(chartab[charind][4], H1);
        if not found1 then
            t1 := &+[ Matrix(phi(h)) : h in H1 ];
            chartab[charind][4][H1] := t1;
        end if;
        found2, t2 := IsDefined(chartab[charind][4], H2);
        if not found2 then
            t2 := &+[ Matrix(phi(h)) : h in H2 ];
            chartab[charind][4][H2] := t2;
        end if;
        vprint FindCovs, 3 : "done.";

        vprint FindCovs, 3 : "Determining image...";
        /* TODO: Note and check the order here */
        im := Image(t1*t2);
        vprint FindCovs, 3 : "done.";
        vprint FindCovs, 3 : "Determining rank...";
        chartab[charind][3][ [H1, H2] ] := im;
        vprint FindCovs, 3 : "done.";
    end if;
    Append(~ims, [* im, mult *]);
end for;
return ims, chartab;

end function;


function TestRanks(extcov, facs, gdiff, chartab, dctab : OnlyGenera := false);
/* Tests wh0ether the Jacobian of the extended cover extcov gets a non-trivial
 * part of the Prym from another group. The second argument facs contains the
 * intervening representation as a combination of characters. */

monG, G, HE, HX := Explode(extcov);
//dctab := [* [ rec`subgroup : rec in Subgroups(G) ], AssociativeArray() *];
HCs0 := dctab[1]; HCs := [ ];
for HC in HCs0 do
    if not IsDefined(dctab[2], [ HE, HX, HC ]) then
        /* Only take curves whose genus is at most that of the Prym (otherwise
         * we would be reduced to another decomposition problem) */
        //monC, gC := MonodromyAndGenusIfBaseRational(extcov, HC);
        if false then
            HCsnew := [ ];
        else
            NC := Normalizer(G, HC);
            if OnlyGenera then
                NE := Normalizer(G, HE); NX := Normalizer(G, HX);
                reps := DoubleCosetRepresentatives(G, NC, NE meet NX);
            else
                /* TODO: Is smaller set also possible here if we take double cosets
                 * in G instead of NG? */
                //NE := Normalizer(G, HE); NX := Normalizer(G, HX);
                //reps := DoubleCosetRepresentatives(NG, NC, NE meet NX);
                reps := DoubleCosetRepresentatives(G, NC, sub< G | [ ] >);
            end if;
            HCsnew := [ HC^rep : rep in reps ];
        end if;
        dctab[2][[ HE, HX, HC ]] := HCsnew;
    end if;
    HCs cat:= dctab[2][[ HE, HX, HC ]];
end for;

vprint FindCovs, 3 : "Testing ranks for a fixed cover...";
HCIms := [ ];
//print facs; print #HCs;
for HC in HCs do
    imsE, chartab := ImagesOfProjection(facs, G, HC, HE, chartab);
    //vprint FindCovs, 3 :"Images for E:", imsE;
    rkE := &+[ Dimension(imE[1])*imE[2] : imE in imsE ];
    if rkE ne 0 then continue; end if;

    imsX, chartab := ImagesOfProjection(facs, G, HC, HX, chartab);
    //vprint FindCovs, 3 :"Images for X:", imsX;
    rkX := &+[ Dimension(imX[1])*imX[2] : imX in imsX ];
    if rkX ne 0 then
        vprint FindCovs, 3 : "Part of Prym";
        /* Per entry, the first two arguments store group and rank, while
         * precise information is stored in the third argument */
        Append(~HCIms, [* HC, rkX, imsX *]);
    else
        vprint FindCovs, 3 : "Not part of Prym";
    end if;
end for;
vprint FindCovs, 3 : "done testing ranks.";
return Append(extcov, HCIms), chartab, dctab;

end function;


intrinsic FilterPryms(extcovs::SeqEnum : OnlyGenera := false) -> .
{For the extended covers in extcovs, determines whether their Jacobian gets a non-trivial part of the Prym from another group. Note that these need not give the full Prym up to isogeny.}

if #extcovs eq 0 then return [ ]; end if;
extcov := extcovs[1]; monG, G0, HE, HX := Explode(extcov);
_, gE := MonodromyAndGenusIfBaseRational(extcov, HE);
_, gX := MonodromyAndGenusIfBaseRational(extcov, HX);
gdiff := gX - gE;

/* Initialize extended character table */
if assigned G0`chartab then
    chartab := G0`chartab;
else
    chartab := CharacterTable(G0);
    chartab := [ [* char *] : char in chartab ];
end if;
/* Initialize subgroup array */
if assigned G0`dctab then
    dctab := G0`dctab;
else
    dctab := [* [ rec`subgroup : rec in Subgroups(G0) ], AssociativeArray() *];
end if;

extcovsnew := [ ];
for extcov in extcovs do
    monG, G, HE, HX := Explode(extcov);
    /* Ensure uniformity of group */
    assert G eq G0;

    /* Determine multiplicities for monG */
    facs := ChevalleyWeilDecomposition(monG, G);
    vprint FindCovs, 2 : "";
    vprint FindCovs, 2 : "Intervening characters:";
    vprint FindCovs, 2 : facs;

    /* Sum resulting projection formula part by part */
    extcovnew, chartab, dctab := TestRanks(extcov, facs, gdiff, chartab, dctab : OnlyGenera := OnlyGenera);
    Append(~extcovsnew, extcovnew);
end for;
G0`chartab := chartab; G0`dctab := dctab;
return extcovsnew, chartab, dctab;

end intrinsic;


intrinsic TestFullPrymGenerated(extcov::List) -> BoolElt
{Test whether the curves C in the final entry of extcov generate the full Jacobian (rather than an abelian subvariety).}

monG, G, HE, HX, HCIms0 := Explode(extcov);
_, gX := MonodromyAndGenusIfBaseRational(extcov, HX);
_, gE := MonodromyAndGenusIfBaseRational(extcov, HE);

HCIms := HCIms0;
/* TODO: For now we only take full pieces */
HCIms := [ ];
for tup in HCIms0 do
    HC := tup[1]; rk := tup[2];
    _, gC := MonodromyAndGenusIfBaseRational(extcov, HC);
    if gC eq rk then
        Append(~HCIms, tup);
    end if;
end for;

/* Take linear-algebraic part of image */
ims := [ HCIm[3] : HCIm in HCIms ];
if #ims eq 0 then return false, 0; end if;
rk := 0;
for i:=1 to #ims[1] do
    /* For relevant parts of H^0 (Z, omega_Z), check dimension obtained by
     * summing individual components with multiplicity */
    Ws := [ im[i][1] : im in ims ];
    mult := [ im[i][2] : im in ims ][1];
    dim := Dimension(&+Ws);
    rk +:= mult*dim;
end for;
return rk eq gX - gE, rk;

end intrinsic;


intrinsic PrymData(extcovs::SeqEnum : OnlyGenera := false) -> .
{Returns information on the various Pryms in the diagram, in particular to distinguish hyperelliptic and non-hyperelliptic cases.}

data := [ ]; reps := [ ];
numnhg := 0; numnhb := 0; numhg := 0; numhb := 0;
for extcov in extcovs do
    monG, G, HE, HX, HCIms := Explode(extcov);
    testZ := IsHyperellipticFromCover(extcov, sub< G | [ ] >);
    testX := IsHyperellipticFromCover(extcov, HX);
    isgood := #extcov[5] ne 0;
    if not testX then
        if isgood then numnhg +:= 1; else numnhb +:= 1; end if;
    else
        if isgood then numhg +:= 1; else numhb +:= 1; end if;
    end if;

    testgen, rk := TestFullPrymGenerated(extcov);
    if testgen then
        testgen := "true";
    else
        if OnlyGenera then
            testgen := "unknown, please set OnlyGenera to false";
        else
            testgen := "false " cat Sprint(rk);
        end if;
    end if;

    genrankseq := [ ];
    for tup in HCIms do
        HC := tup[1]; rk := tup[2];
        _, gC := MonodromyAndGenusIfBaseRational(extcov, HC);
        Append(~genrankseq, [* HC, gC, rk *]);
    end for;

    datum := [* testZ, testX, testgen, genrankseq *];
    if not datum in data then
        Append(~data, datum);
        Append(~reps, extcov);
    end if;
end for;
nums := [ [ numnhg, numnhb ], [ numhg, numhb ] ];
return data, reps, nums;

end intrinsic;


intrinsic PrintPrymData(extcovs::SeqEnum : OnlyGenera := false, GenRank := true)
{Prints information on the various Pryms in the diagram.}

//print "";
//print "===== Prym data =====";

extcov := extcovs[1]; G := extcov[2];
_, gZ := MonodromyAndGenusIfBaseRational(extcov, sub< G | [ ] >);
print "";
print "Monodromy group:";
print GroupName(G);
print "Order:";
print #G;
print "Genus of Galois closure:";
print gZ;

data, reps, nums := PrymData(extcovs : OnlyGenera := OnlyGenera);
numnhg, numnhb := Explode(nums[1]);
numhg, numhb := Explode(nums[2]);

print "";
print "Number of different Prym data types:";
print #data;
print "Number of good non-hyperelliptic curves:";
print numnhg;
print "Number of bad non-hyperelliptic curves:";
print numnhb;
print "Number of good hyperelliptic curves:";
print numhg;
print "Number of bad hyperelliptic curves:";
print numhb;

for i:=1 to #data do
    testZ, testX, testgen, genrankseq := Explode(data[i]);
    print "";
    print "----------------------------------------";
    print "Type", i;

    print "";
    print "Z hyperelliptic from cover?";
    print testZ;
    print "X hyperelliptic from cover?";
    print testX;
    print "Full Prym generated?";
    print testgen;

    /* TODO: May want to remove this line at some point */
    genrankseq := [ tup : tup in genrankseq | tup[2] eq tup[3] ];
    if GenRank then
        print "Genera for relevant subgroups:";
        print [ [* #tup[1], GroupName(tup[1]), tup[2] *] : tup in genrankseq ];
    end if;
end for;

end intrinsic;


/* After this, one can call PrintExtendedCoverData with the final entries of
 * the extcov in reps to get information on the lattice of curves giving a
 * contribution to the Prym, et cetera. */


intrinsic PrymOperatorRank(monG::SeqEnum, G::Grp, HX::Grp, HY::Grp) -> .
{Finds the rank of the image of Jac (X) --> Jac (Y), as well as the relevant
genera. The cover monG has to have a base of genus 0 for the genera returned to
be correct.}

assert &and[ sigma in G : sigma in monG ];
assert HX meet G eq HX; assert HY meet G eq HY;

extcov := [* monG, G *];
_, gX := MonodromyAndGenusIfBaseRational(extcov, HX);
_, gY := MonodromyAndGenusIfBaseRational(extcov, HY);

if assigned G`chartab then
    chartab := G`chartab;
else
    chartab := CharacterTable(G);
    chartab := [ [* char *] : char in chartab ];
end if;

facs := ChevalleyWeilDecomposition(monG, G);
imsY, chartab := ImagesOfProjection(facs, G, HX, HY, chartab);
rk := &+[ Dimension(imY[1])*imY[2] : imY in imsY ];
return rk, gX, gY;

end intrinsic;
