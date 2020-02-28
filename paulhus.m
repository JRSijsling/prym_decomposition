declare verbose FindCovs, 3;

/* genvectors.mag

Last Updated: May 10, 2016

These functions are primarily Magma versions of GAP programs
written by Thomas Breuer.

Breuer, Thomas. Characters and automorphism groups of compact Riemann surfaces. London Mathematical Society Lecture Note Series,  v. 280. Cambridge University Press, Cambridge, 2000.

The original GAP code has the following copyright:
Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany

We are grateful to Thomas Breuer for permission to post the Magma version of this code.

Functions:
ConvertToPerm(G)

CardinalityOfHom(C, g0, tbl, classlengths, ordG)
NonGenerationByScottCriterion(tbl, C, sizeconjclass, ordG)
WeakTestGeneration(C, g0, G)
HardTestGeneration(C, g0, G)
RepresentativesEpimorphisms(signature, G)

Procedure:
AddMonodromy(g)

*/



Z:=Integers();   /* Used for coersion below */

SetColumns(0);  /* Better Printing */



/* ***************************************
ConvertToPerm(G)

Inputs: G            group

Outputs: a group of type GrpPerm in Magma

Based on Magma algorithm here:
http://magma.maths.usyd.edu.au/magma/handbook/text/705#7874


************************************ */

ConvertToPerm:=function(G);

if   Type(G) eq GrpPC then
   SL := Subgroups(G);
   T := {X`subgroup: X in SL};
   TrivCore := {H:H in T| #Core(G,H) eq 1};
   mdeg := Min({Index(G,H):H in TrivCore});
   Good := {H: H in TrivCore| Index(G,H) eq mdeg};
   H := Rep(Good);
   f,G,K := CosetAction(G,H);
end if;

return G;

end function;



/* ***************************************
CardinalityOfHom( C, g0, tbl, classlengths,ordG)

Inputs: C
        g0           orbit genus
        tbl          character table of a group G
        classlength  list of size of each conj class
        ordG         order of a group G



Outputs: the cardinality of Hom_C(g_0,G) computed using
         a result of Jones (Section 14 of Breuer)


Used in WeakTestGeneration
************************************ */

CardinalityOfHom := function( C, g0, tbl ,classlength, ordG)

r:=#C;
M:=[];

for i in [ 1 .. r ] do
   if C[i] in Z then
      M[i]:= [C[i]];
   else
      M[i]:=C[i];
   end if;
end for;
C:=M;

exp:= 2 - 2*g0 - r;
sum:=0;

for i in [1..#tbl] do
   chi:=tbl[i];
   product:=1;
   for Ci in C do
      temp:=0;
      for j in [1..#Ci] do
         temp:=temp+chi[Ci[j]]*classlength[Ci[j]];
      end for;
   product:=product*temp;
   end for;
   sum:=sum+(chi[1]^exp*product);
end for;

sum:=Rationals()!sum;

return ordG^( 2*g0 - 1 )* sum;

end function;





/* ***************************************
NonGenerationByScottCriterion(tbl, C, sizeconjclass, ordG )

Tests the Nongeneration Criterion of Scott
    (Section 15.3 in Breuer)

Input:  Character Table of a group
        C list of
        sizeconjclass
        ordG   The order of the group G


Output: true if the nongeneration criterion of Scott
           confirms that there is no epimorphism
        false otherwise

Used in: WeakTestGeneration

************************************ */

NonGenerationByScottCriterion := function( tbl,C,G,Con)


for chi in tbl do
   degree:= chi[1];
   dim:= 2 * ( degree - InnerProduct( chi,tbl[1]));

   for i in C do
      xi:= Con[i,3];
      S:=sub<G|xi>;
      Ts:=CharacterTable(S);
      dim:= dim - degree + InnerProduct(Restriction(chi,S) ,Ts[1]);
   end for;

   if 0 lt dim then
      return true;
   end if;
end for;

return false;

end function;





/* ***************************************
WeakTestGeneration(C, g0, G)

Inputs:  C the class structure of G
         g0 the orbit genus
         G a finite group

Outputs: false if Epi_C(g,G) is empty based on
            Nongeneration criterion of Scott or
            conditions on the cardinality of Hom
            (Section 15.1 of Breuer)

         true otherwise

Used in RepresentativesEpimorphisms
************************************ */

WeakTestGeneration := function( C, g0, G )

tbl:= CharacterTable( G );
size:=#G;
Con:=ConjugacyClasses(G);
numb:=0;
sizeconjclass:=[];

for i in [1..#Con] do
   if Con[i][2] eq 1 then
      numb:=numb+1;
   end if;
   Append(~sizeconjclass,Con[i][2]);
end for;

if CardinalityOfHom(C, g0, tbl, sizeconjclass,size) lt size/numb  then
   return false;
elif g0 eq 0 and NonGenerationByScottCriterion( tbl, C, G, Con ) then
   return false;
end if;

return true;

end function;





/* ***************************************
HardTestGeneration(C, g0, G)

Inputs:  C the class structure of G
         g0 the orbit genus
         G a finite group


Outputs: tup   which is a list of elements of G
               representing the monodromy

         [id_G,id_G]  otherwise


Used in RepresentativesEpimorphisms

************************************ */

HardTestGeneration := function( C, g0, G )

r:=#C;
n:=#( G );
id:=Identity(G);


Con:=ConjugacyClasses(G);
sigma:=[];   /* list of representatives of conjugacy classes */
for i in [1..r] do
   Append(~sigma,Con[C[i]][3]);
end for;


rep_cen:=[]; /* list of centralizers for each element of sigma */
for s in sigma do
   Append(~rep_cen,Centralizer(G,s));
end for;

/*Initialize iteration */
if 0 lt  r then
   iter_cen:= [rep_cen[1]];
   R:= [[id]];
else
   iter_cen:= [];
   R:= [];
end if;


for i in [ 2 .. r-1 ] do
   R[i]:= DoubleCosetRepresentatives(G, rep_cen[i],iter_cen[i-1] );
   iter_cen[i]:= iter_cen[i-1] meet Centralizer(G,sigma[i]^R[i][1] );
end for;


if 1 lt  r then
   R[r]:= DoubleCosetRepresentatives( G, rep_cen[r], iter_cen[r-1] );
end if;

max:=[];
for i in [1..#R] do
   Append(~max,#R[i]);
end for;

    /* List of all ones  */
choice:= [];
for i in [1..r] do
   Append(~choice,1);
end for;

     /* list of sigma[i]^R[i][1]; */
tuple:=[];
for i in [1..r] do
   Append(~tuple, sigma[i]^R[i][1] );
end for;



/* function: NextElementTuple */

NextElementTuple:= function(choice, bleck, iter_cen, R, max)


  pos:= r;
  while 1 lt pos and choice[pos] eq max[pos] do
     pos:= pos - 1;
  end while;
  if pos le 1 then
     return choice, [id,id], iter_cen, R, max;
  end if;


  choice[pos]:= choice[pos] + 1;
  bleck[pos]:= sigma[pos]^R[pos][choice[pos]];
  if pos lt r then
     iter_cen[pos]:= iter_cen[pos-1] meet  Centralizer(G,sigma[pos]^R[pos][choice[pos]]);
     pos:= pos + 1;
     while pos le r do
        R[pos]:= DoubleCosetRepresentatives(G, rep_cen[pos], iter_cen[pos-1]);
        bleck[pos]:= sigma[pos]^R[pos][1];
        choice[pos]:= 1;
        max[pos]:= #R[pos] ;
       iter_cen[pos]:=iter_cen[pos-1] meet Centralizer(G,sigma[pos]^R[pos][1]);
        pos:= pos + 1;
     end while;

   end if;


   return choice, bleck, iter_cen, R, max;
end function;



tup:= tuple;
genvecs:=[];

while tup ne [id,id] do


   prod:= id;
   for i in [1..r] do
      prod:= prod * tup[i];
   end for;



   if g0 eq 0 then
      if prod eq  id and #sub<G | tup >  eq  n then

         hypgens:=[];

         for t in tup do
            Append(~hypgens,t);
         end for;

        Append(~genvecs, hypgens);


      end if;

      else
        ReduceGenerators(~G);  /* removes redundancies */

      if   prod  eq  id and NumberOfGenerators(G)  le g0 then

      hypgens:=[];
      for h in Generators(G) do
         Append(~hypgens,h);
         Append(~hypgens,id);
      end for;

      for i in [#hypgens+1..2*g0] do
         Append(~hypgens,id);
      end for;

      for t in tup do
          Append(~hypgens,t);
      end for;

      Append(~genvecs, hypgens);




   elif prod eq id and IsAbelian(G) and NumberOfGenerators(G) le  2*g0 then

      hypgens:=Generators(G);
      hypgens:=SetToSequence(hypgens);

      for i in [#hypgens+1..2*g0] do
         Append(~hypgens,id);
      end for;

      for t in tup do
         Append(~hypgens,t);
      end for;

        Append(~genvecs, hypgens);



   else

      elms:=[];

      for h in G do
         Append(~elms,h);
      end for;


      counter:=[];
      counter[1]:= 0;
      for i in [2..2*g0] do
         Append(~counter,1);
      end for;

      repeat
         i:= 1;
         while i le 2*g0 and counter[i] eq n do
            counter[i]:= 1;
            i:= i+1;
         end while;

         if i le 2*g0 then
            counter[i]:=counter[i] + 1;
            commprod:= id;
            for j in [1..g0] do
               commprod:=commprod*(elms[counter[2*j-1]], elms[counter[2*j]]);
                  /* commutator is (g,h) */
            end for;


            if commprod*prod eq id then


               tempelms:=[];
               for c in counter do
                  Append(~tempelms,elms[c]);
               end for;

               H:=tup;
               for h in tempelms do
                  Append(~H,h);
               end for;

               if #sub<G|H> eq n then

                     for t in tup do
                        Append(~tempelms, t);
                     end for;

             Append(~genvecs, tempelms);

               end if;
            end if;
         end if ;
         until i  gt  2*g0;
      end if;  end if;



   choice, tup, iter_cen, R, max:= NextElementTuple(choice, tup, iter_cen, R, max);

end  while;


if #genvecs gt 0 then
   return genvecs;
else
   return [[id,id]];
end if;

end function;


/* Additions and intrinsics follow */

intrinsic ConjugacyClassNumber(G::GrpPerm, g::GrpPermElt) -> Tup
{Returns the conjugacy class number for g in the set of conjugacy classes of G.
Note that this output is inconsistent, but not after the classes have been
calculated once.}
CCG := ConjugacyClasses(G);
for i:=1 to #CCG do
    if IsConjugate(G, g, CCG[i][3]) then
        return i;
    end if;
end for;
end intrinsic;


intrinsic CoversFromClasses(G::Grp, g0::RngIntElt, Cs::SeqEnum) -> .
{Determines the covers, if any, of a curve of genus g0 whose ramification
corresponds to the list of conjugacy classes Cs.}

if Type(Cs[1]) eq GrpPermElt then
    Cs := [ ConjugacyClassNumber(G, C) : C in Cs ];
elif Type(Cs[1]) eq Tup then
    Cs := [ ConjugacyClassNumber(G, C[3]) : C in Cs ];
end if;

if not Type(Cs[1]) eq RngIntElt then
    error "Cs is not decent";
end if;

if not WeakTestGeneration(Cs, g0, G) then
    return [ ];
end if;

covs := HardTestGeneration(Cs, g0, G);
if covs eq [ [ Identity(G), Identity(G) ] ] then
    return [ ];
end if;
return covs;

end intrinsic;


intrinsic ListUpToEquivalence(L::SeqEnum, comp::UserProgram) -> .
{Entries in L distinct under comparison by the function comp.}

L0 := [ ];
for x in L do
    add := true;
    for x0 in L0 do
        if comp(x, x0) then add := false; break; end if;
    end for;
    if add then Append(~L0, x); end if;
end for;
return L0;

end intrinsic;


intrinsic CoversFromRamification(G::Grp, g0::RngIntElt, typs::SeqEnum : AmbIso := true) -> .
{Determines the covers, if any, of a curve of genus g0 whose ramification types
are given by typs. If G has non-trivial normalizer and AmbIso is
set to false, then there may be duplicates in this list. If AmbIso
is set to true, as is the case by default, then we check for isomorphism as
covers whose degree equals that of G as a permutation group. This may take
some time.}

CCG := ConjugacyClasses(G);
Css := [ [ C : C in CCG | CycleStructure(C[3]) eq typ ] : typ in typs ];

covs := [ ];
for tup in CartesianProduct(Css) do
    covs cat:= CoversFromClasses(G, g0, [ C : C in tup ]);
end for;
assert &and[ &and[ g in G : g in cov ] : cov in covs ];
assert &and[ sub< G | cov > eq G : cov in covs ];

vprint FindCovs : "Number before for ambient isomorphism:";
vprint FindCovs : #covs;
if not AmbIso then return covs; end if;

vprint FindCovs : "Checking for ambient isomorphism...";
S := SymmetricGroup(Degree(G));
N := Normalizer(S, G);
if N eq G then
    vprint FindCovs : "done.";
    return covs;
end if;
reps := DoubleCosetRepresentatives(N, G, sub< G | [ ] >);

function CompInS(cov1, cov2)
    for rep in reps do
        if &and[ cov1[i]^rep eq cov2[i] : i in [1..#cov1] ] then
            return true;
        end if;
    end for;
    return false;
end function;

covs := ListUpToEquivalence(covs, CompInS);
vprint FindCovs : "done.";
return covs;

end intrinsic;


intrinsic CoversFromClassesSample(G::Grp, g0::RngIntElt, Cs::SeqEnum, ncovs::RngIntElt) -> .
{Determines the covers, if any, of a curve of genus g0 whose ramification
corresponds to the list of conjugacy classes Cs.}

assert g0 eq 0;
if Type(Cs[1]) eq GrpPermElt then
    Cs := [ ConjugacyClassNumber(G, C) : C in Cs ];
elif Type(Cs[1]) eq Tup then
    Cs := [ ConjugacyClassNumber(G, C[3]) : C in Cs ];
end if;

if not Type(Cs[1]) eq RngIntElt then
    error "Cs is not decent";
end if;

Con := ConjugacyClasses(G);
Cs := [ Con[num] : num in Cs ];
covs := [ ]; counter := 0;
while counter lt 10*ncovs do
    covdeb := [ Cs[i][3]^(Random(G)) : i in [1..(#Cs - 1)] ];
    covfin := (&*covdeb)^(-1);
    if IsConjugate(G, covfin, Cs[#Cs][3]) then
        cov := covdeb cat [ covfin ];
        if sub< G | cov > eq G then
            assert Order(&*cov) eq 1;
            Append(~covs, covdeb cat [ covfin ]);
            if #covs eq ncovs then
                return covs;
            end if;
        end if;
    end if;
    counter +:= 1;
    //print counter;
end while;
return covs;

end intrinsic;


intrinsic CoversFromRamificationSample(G::Grp, g0::RngIntElt, typs::SeqEnum, ncovs::RngIntElt : AmbIso := true) -> .
{Determines the covers, if any, of a curve of genus g0 whose ramification types
are given by typs. If G has non-trivial normalizer and AmbIso is
set to false, then there may be duplicates in this list. If AmbIso
is set to true, as is the case by default, then we check for isomorphism as
covers whose degree equals that of G as a permutation group. This may take
some time.}

assert g0 eq 0;
CCG := ConjugacyClasses(G);
Css := [ [ C : C in CCG | CycleStructure(C[3]) eq typ ] : typ in typs ];

covs := [ ]; counter := 0;
for tup in CartesianProduct(Css) do
    //counter +:= 1; print counter;
    covs cat:= CoversFromClassesSample(G, g0, [ C : C in tup ], ncovs);
end for;
assert &and[ &and[ g in G : g in cov ] : cov in covs ];
assert &and[ sub< G | cov > eq G : cov in covs ];

vprint FindCovs : "Number before for ambient isomorphism:";
vprint FindCovs : #covs;
if not AmbIso then return covs; end if;

vprint FindCovs : "Checking for ambient isomorphism...";
S := SymmetricGroup(Degree(G));
N := Normalizer(S, G);
if N eq G then
    vprint FindCovs : "done.";
    return covs;
end if;
reps := DoubleCosetRepresentatives(N, G, sub< G | [ ] >);

function CompInS(cov1, cov2)
    for rep in reps do
        if &and[ cov1[i]^rep eq cov2[i] : i in [1..#cov1] ] then
            return true;
        end if;
    end for;
    return false;
end function;

covs := ListUpToEquivalence(covs, CompInS);
vprint FindCovs : "done.";
return covs;

end intrinsic;
