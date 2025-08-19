
(*TODO: 
1. unify fset lemmas 
*)

Require Export Setoid RelationClasses Morphisms.
Require Export List.
Require Export ZArith OrdersFacts OrderedTypeEx.
Require Export String.


Require Import Coq.Program.Equality.
Require Export DecidableType.
Require Export DecidableTypeEx.
Require Export FSetWeakList FSetFacts FSetProperties FSetDecide. 
Require Export MSetWeakList.
Require Export ListSet.

From mathcomp Require Export ssrfun ssrbool eqtype. 
Require Import Coq.Lists.List.
Import ListNotations.
Require Export FMapWeakList FMapFacts FMapInterface.
Require Import Coq.FSets.FSetProperties. (*must be importted after the three above*)
Require Import Coq.FSets.FSetFacts. (*must be importted after the three above*)

Require Import Coq.FSets.FSetEqProperties. (*must be importted after the three above*)
Require Import Coq.FSets.FSetDecide.

Require Export Program.Basics Program.Tactics Program.Syntax.

Require Import JMeq.

Set Bullet Behavior "Strict Subproofs".

Definition var := nat.
Definition alloc := 0.
Definition this:var := 1.
Definition ret:var := 2.
(*parameters*)
Definition xx:var := 3.

(*local variables*)
Definition xx1:var := 4.
Definition xx2:var := 5.
Definition xx3:var := 6.

Global Hint Unfold alloc : namesdb.
Global Hint Unfold this : namesdb.
Global Hint Unfold ret : namesdb.
Global Hint Unfold xx : namesdb.
Global Hint Unfold xx1 : namesdb.
Global Hint Unfold xx2 : namesdb.
Global Hint Unfold xx3 : namesdb.

Ltac solve_names := autounfold with namesdb;simpl;auto.
Module natnat_DT := PairUsualDecidableType Nat_as_DT Nat_as_DT.
Module ptrnat_DT := PairUsualDecidableType natnat_DT Nat_as_DT.

Module NM  := FMapWeakList.Make(Nat_as_DT).
Module PNM := FMapWeakList.Make(ptrnat_DT).
Module PS := FSetWeakList.Make(natnat_DT).
Module PNS := FSetWeakList.Make(ptrnat_DT).
Module NS  := FSetWeakList.Make(Nat_as_DT).

Module PNS' := WProperties_fun (ptrnat_DT) PNS. 
Module PS' := WProperties_fun (natnat_DT) PS. 
Module NS' := WProperties_fun (Nat_as_DT) NS.
Module PNS_ := WFacts_fun  (ptrnat_DT) PNS. 
Module PS_ := WFacts_fun  (natnat_DT) PS. 
Module NS_ := WFacts_fun  (Nat_as_DT) NS.

Module PNSPEQ := WEqProperties_fun (ptrnat_DT) PNS. 
Module NSEQ := WEqProperties_fun (Nat_as_DT) NS. 
Module PSEQ := WEqProperties_fun (natnat_DT) PS. 


Module NSDecide := Decide NS.
Module PSDecide := Decide PS.
Module PNSDecide := Decide PNS.
Module NM_ := FMapFacts.WFacts_fun (Nat_as_DT) NM. 
Module NM' := FMapFacts.WProperties_fun Nat_as_DT NM.

Notation "⌊ F ⌋ y ▹ x" := (NS.fold F y x) (at level 40).
Notation "⌊' F '⌋ y ▹ x" := (PS.fold F y x) (at level 40).
Notation "⌊'' F ''⌋ y ▹ x" := (PNS.fold F y x) (at level 40).
Notation "⌈ F ⌉ y ▹ x" := (NM.fold F y x) (at level 40).

Require Import Lia.
Lemma temp1: forall X Y x, NS.Equal X Y -> NS.Equal (NS.remove x X) (NS.remove x Y).
NSDecide.fsetdec.
Defined.

Lemma andbb: forall (a b:bool), a -> b -> a && b.
Proof.
  intros. rewrite H. rewrite H0.
  auto.
Defined.
(*really wired that if apply impbb1 to some (a ==> b) assumption will get uninitialized b*)
Lemma impbb1: forall a b,  (implb a b = true) -> a =true -> b = true.
Proof.
  intros. rewrite H0 in H. simpl in H. auto. 
Defined.
Lemma impbb: forall (a b:bool), (a -> b) -> a ==> b.
Proof.
  intros. case_eq(a);simpl;auto.
Defined.
Definition compssubset x y := PS.subset ( x) ( y) && negb (PS.equal ( x) ( y)).

Definition StrictSubset := fun X Y => PS.Subset X Y /\ (~PS.Equal X Y).

Lemma cssub_ssub: forall X Y, compssubset X Y <-> StrictSubset X Y.
Proof.
  intros. 
  unfold compssubset. unfold StrictSubset. 
  constructor;intros.
  apply andb_prop in H. destruct H. constructor.
  apply PS.subset_2;auto.
  unfold not;intros. apply PS.equal_1 in H1. rewrite H1 in H0. simpl in H0. inversion H0.

  destruct H. apply andbb.
  apply PS.subset_1;auto. unfold negb. case_eq(PS.equal X Y);intros. apply PS.equal_2 in H1. apply H0 in H1;contradiction.
  auto.
Defined.

  
  

Lemma temp2: forall X Y x, ~ PS.Equal X Y -> PS.In x X -> PS.In x Y -> ~ PS.Equal (PS.remove x X) (PS.remove x Y).
(*{1,2,3} {2,3}, remove 1 become equal, must remove one that in *)
(*{1,2,3} {2,3,4}, remove 2 become equal, must remove one that in *)
  intros. 
  unfold not. intros. 
  assert (PS.Equal (PS.add x (PS.remove x X)) (PS.add x (PS.remove x Y))).
  PSDecide.fsetdec.
  assert (PS.Equal (PS.add x (PS.remove x X)) X). apply PS'.add_remove;auto.
  assert (PS.Equal (PS.add x (PS.remove x Y)) Y). apply PS'.add_remove;auto.
  rewrite H4 in H3. rewrite H5 in H3. auto.
   
Defined.
Lemma ex1: forall X Y, StrictSubset X Y -> exists e, PS.In e Y /\ ~PS.In e X.
  apply (@PS'.set_induction (fun X => forall (Y : PS.t), StrictSubset X Y -> exists e : PS.elt, PS.In e Y /\ ~ PS.In e X)).
  intros. unfold StrictSubset in H0.
  destruct H0. assert (~PS.Equal PS.empty Y).
  assert (PS.Equal s PS.empty). PSDecide.fsetdec. unfold not. intros.
  assert (PS.Equal s Y). PSDecide.fsetdec. apply H1 in H4. auto. 
  assert (PS.is_empty Y = false). case_eq(PS.is_empty Y);auto;intros.
  apply PS.is_empty_2 in H3. assert (PS.Equal PS.empty Y). PSDecide.fsetdec. apply H2 in H4. contradiction. 
  apply PSEQ.choose_mem_3 in H3. destruct H3 as [ele eleprop]. destruct eleprop. 
  exists ele. constructor. apply PS.mem_2. auto. PSDecide.fsetdec.

  intros.
  assert (StrictSubset s (PS.remove x Y)).
  apply PS'.Add_Equal in H1. 
  unfold StrictSubset in H2. destruct H2. unfold StrictSubset. constructor.
  rewrite H1 in H2. PSDecide.fsetdec.
  rewrite H1 in H3. 
  assert (PS.Equal (PS.remove x (PS.add x s)) s). PSDecide.fsetdec.
  unfold not. intros.
  rewrite <-H4 in H5. 
  apply temp2 with (x:=x) in H3;auto. PSDecide.fsetdec. 
  rewrite H1 in H2. PSDecide.fsetdec.
  
  apply H in H3. 
  destruct H3 as [e ep]. destruct ep.
  assert (~PS.E.eq e x). apply PS_.remove_iff in H3. destruct H3;auto. 
  exists e. constructor. PSDecide.fsetdec.
  unfold not. intros. assert (~PS.E.eq x e). PSDecide.fsetdec. apply PS.add_3 with (s:=s) in H7. apply H4 in H7. auto. 
  apply PS'.Add_Equal in H1.  rewrite <- H1. auto.
Qed.
  (*s' = s + x*)
  (*s' < Y*)
  (*s + x <> Y*)
  (*s + x - x <> Y - x*)

  (*s < Y - x*)
  (*exists e, e in Y - x /\ ~ e in s*)
  (*we know what e <> x*)
  (*need, exists e, e in Y /\ ~ e in s + x*)

Lemma cardinal_strict_subset (s t : PS.t) :
  StrictSubset s t -> PS.cardinal s < PS.cardinal t.
  intros.
  apply ex1 in H as HH. destruct HH. destruct H0.
  unfold StrictSubset in H. destruct H.
  apply PS'.subset_cardinal_lt with x;auto.
Defined.
Require Import Coq.Wellfounded.Inclusion.
Lemma wf_strict_subset' : well_founded StrictSubset.
Proof.
  unfold StrictSubset.
  pose (well_founded_ltof PS.t (PS.cardinal)) as HH.
  apply wf_incl with ((Wf_nat.ltof PS.t PS.cardinal)).
  unfold inclusion. unfold Wf_nat.ltof.
  apply cardinal_strict_subset. auto.
Qed.

Import PNS'.
Import PNS_.
Lemma fold_equal: forall f i s s', NS.Equal s s' -> PNS.Equal (⌊ f ⌋ s ▹ i) (⌊ f ⌋ s' ▹ i).
Proof.
  intros. apply NS'.fold_equal;auto.
Admitted.
(* Lemma fold_empty: forall f i,  (⌊ f ⌋ NS.empty ▹ i) = i.
Proof.
  intros. rewrite NS'.fold_empty. PNSDecide.fsetdec. 
Defined. *)
Lemma fold_add: forall f i s x, ~NS.In x s -> PNS.Equal (⌊ f ⌋ (NS.add x s) ▹ i) (f x (⌊ f ⌋ s ▹ i)).
Proof.
  intros. apply NS'.fold_add;auto.
Admitted.
(* Lemma fold_equal: forall f i s s', NS.Equal s s' -> PNS.Equal (⌊ f ⌋ s ▹ i) (⌊ f ⌋ s' ▹ i).
Proof.
  intros. apply NS'.fold_equal;auto.
Admitted. *)
Lemma fold_empty_ps: forall f i, PNS.Equal (⌊' f '⌋ PS.empty ▹ i) i.
Proof.
  intros. rewrite PS'.fold_empty. PNSDecide.fsetdec. 
Defined.




Lemma fold_add_ps: forall f i s x, ~PS.In x s -> PNS.Equal (⌊' f '⌋ (PS.add x s) ▹ i) (f x (⌊' f '⌋ s ▹ i)).
Proof.
  intros. apply PS'.fold_add;auto.
Admitted.

Lemma fold_equal_pns: forall f i s s', PNS.Equal s s' -> PS.Equal (⌊'' f ''⌋ s ▹ i) (⌊'' f ''⌋ s' ▹ i).
Proof.
  intros. apply PNS'.fold_equal;auto.
Admitted.
Lemma fold_add_pns: forall f i s x, ~PNS.In x s -> PS.Equal (⌊'' f ''⌋ (PNS.add x s) ▹ i) (f x (⌊'' f ''⌋ s ▹ i)).
Proof.
  intros. apply PNS'.fold_add;auto.
Admitted.


Notation "A ⋓ B" := (PNS.union A B) (at level 40).
Notation "A ⋒ B" := (PNS.inter A B) (at level 40).
Notation "⦱" := (PNS.empty) (at level 40).
Notation "{{{ a }}}" := (PNS.singleton a) (at level 39).
Notation "A ⧻ a" := (PNS.add a A) (at level 40).
Notation "A ⩶ B" := (PNS.Equal A B) (at level 40).
Notation "A ⫅ B" := (PNS.Subset A B) (at level 40).

Notation "A ⩅ B" := (PS.union A B) (at level 40).
Notation "A ⩄ B" := (PS.inter A B) (at level 40).
Notation "⦲" := (PS.empty) (at level 40).
Notation "{{ a }}" := (PS.singleton a) (at level 39).
Notation "A ⧺ a" := (PS.add a A) (at level 40).
Notation "A ⩵ B" := (PS.Equal A B) (at level 40).
Notation "A ⫉ B" := (PS.Subset A B) (at level 40).

Notation "A ⊍ B" := (NS.union A B) (at level 40).
Notation "A ⩀ B" := (NS.inter A B) (at level 40).
Notation "A ⨪ B" := (NS.diff A B) (at level 40).
Notation "∅" := (NS.empty) (at level 9).
Notation "{· a ·}" := (NS.singleton a) (at level 40).
Notation "A ⨥ a" := (NS.add a A) (at level 40).
Notation "A ⩦ B" := (NS.Equal A B) (at level 40).
Notation "A ⊆ B" := (NS.Subset A B) (at level 40).


Notation "m [< k ↦ v >]" := (NM.add k v m) (at level 40).
Notation "m [< k >]" := (NM.find k m) (at level 40).
Notation "m '<⍀>' k" := (NM.remove k m) (at level 40).


Lemma andb_prop': forall a b, a && b -> a /\ b.
intros. apply andb_prop in H. destruct H;auto.
Defined. 
Lemma notb_prop': forall b, is_true (negb b) -> b = false.
intros. unfold negb in H. case_eq(b);intros; subst;auto.
Defined.
Lemma notb_prop'': forall b, b = false -> is_true (negb b).
intros. unfold negb in H. case_eq(b);intros; subst;auto.
Defined.

Ltac destruct_conj :=
  match goal with
  | [H: (?b /\ ?c) |- _ ] =>
    let Hb := fresh H in
    let Hc := fresh H in
    (* andb_prop : b && c = true -> b = true /\ c = true *)
    destruct H as [Hb Hc];
    clear H
  end.
Ltac destruct_andb :=
  match goal with
  | [H: is_true (?b && ?c) |- _ ] =>
    let Hb := fresh H in
    let Hc := fresh H in
    (* andb_prop : b && c = true -> b = true /\ c = true *)
    destruct (andb_prop' b c H) as [Hb Hc];
    clear H
  | [H: (?b && ?c) = true |- _ ] =>
    let Hb := fresh H in
    let Hc := fresh H in
    (* andb_prop : b && c = true -> b = true /\ c = true *)
    destruct (andb_prop' b c H) as [Hb Hc];
    clear H
  end.
Ltac handle_notb :=
match goal with
| [H: is_true (negb (?b)) |- _ ] =>
  apply notb_prop' in H
end.

Ltac handle_sets :=
repeat (match goal with
| [H: is_true (PNS.subset ?A ?B) |- _ ] =>
  apply PNS.subset_2 in H
| [H: (PNS.subset ?A ?B) = true |- _ ] =>
  apply PNS.subset_2 in H
| [ |- is_true (PNS.subset ?A ?B) ] =>
  apply PNS.subset_1
| [ |- (PNS.subset ?A ?B) = true] =>
  apply PNS.subset_1

| [H: is_true (PNS.equal ?A ?B) |- _ ] =>
  apply PNS.equal_2 in H
| [H: (PNS.subset ?A ?B) = true |- _ ] =>
  apply PNS.equal_2 in H
| [ |- is_true (PNS.subset ?A ?B) ] =>
  apply PNS.equal_1
| [ |- (PNS.subset ?A ?B) = true] =>
  apply PNS.equal_1

| [H: is_true (PNS.is_empty ?A) |- _ ] =>
  apply PNS.is_empty_2 in H
| [H: (PNS.is_empty ?A) = true |- _ ] =>
  apply PNS.is_empty_2 in H
| [ |- is_true (PNS.is_empty ?A) ] =>
  apply PNS.is_empty_1
| [ |- (PNS.is_empty ?A) = true] =>
  apply PNS.is_empty_1

| [H: is_true (PS.subset ?A ?B) |- _ ] =>
  apply PS.subset_2 in H
| [H: (PS.subset ?A ?B) = true |- _ ] =>
  apply PS.subset_2 in H
| [ |- is_true (PS.subset ?A ?B) ] =>
  apply PS.subset_1
| [ |- (PS.subset ?A ?B) = true] =>
  apply PS.subset_1

| [H: is_true (PS.equal ?A ?B) |- _ ] =>
  apply PS.equal_2 in H
| [H: (PS.subset ?A ?B) = true |- _ ] =>
  apply PS.equal_2 in H
| [ |- is_true (PS.subset ?A ?B) ] =>
  apply PS.equal_1
| [ |- (PS.subset ?A ?B) = true] =>
  apply PS.equal_1

| [H: is_true (NS.mem ?A ?B) |- _ ] =>
  apply NS.mem_2 in H
| [H: (NS.mem ?A ?B) = true |- _ ] =>
  apply NS.mem_2 in H
| [ |- is_true (NS.mem ?A ?B) ] =>
  apply NS.mem_1
| [ |- (NS.subset ?A ?B) = true] =>
  apply NS.mem_1

end).

Lemma eq_dec_refl: forall a, exists H, Nat.eq_dec a a = left H.
intros. case_eq(Nat.eq_dec a a);intros. exists e;auto. contradiction. 
Qed.
Lemma eqb_refl: forall a, Nat.eqb a a = true.
intros. apply Nat.eqb_eq. auto. 
Qed.

Lemma neq_eq_def {a b: var} (neq: a <> b): exists H, Nat.eq_dec a b = right H.
case_eq (Nat.eq_dec a b);intros. assert (False). clear H. apply neq in e. auto. contradiction.
exists n. auto. 
Qed.
Ltac nein neq H := destruct (neq_eq_def neq) as [neq' HH]; rewrite HH in H; clear HH; clear neq'.
Ltac ne neq := destruct (neq_eq_def neq) as [neq' HH]; rewrite HH; clear HH; clear neq'.
Ltac idin a H := destruct (eq_dec_refl a) as [neq' HH]; rewrite HH in H; clear HH; clear neq'.
Ltac id a := destruct (eq_dec_refl a) as [neq' HH]; rewrite HH; clear HH; clear neq'.





Lemma ns_notin_empty: forall x , ~ NS.In x (∅).
Proof.
    intros. NSDecide.fsetdec.
Defined.
Lemma ns_notin_union: forall x A B, ~NS.In x A -> ~NS.In x B -> ~ NS.In x (A ⊍ B).
Proof.
  intros. NSDecide.fsetdec.
Defined.
Lemma ns_notin_add: forall x A y, ~NS.In x A -> x<>y -> ~ NS.In x (A ⨥ y).
Proof.
  intros. NSDecide.fsetdec.
Defined.
Lemma ns_notin_singleton: forall x y, x<>y -> ~ NS.In x ({·y·}).
Proof.
  intros. NSDecide.fsetdec.
Defined.


Lemma ns_disj_empty: forall A, NS.Empty ((∅) ⩀ A).
Proof.
    intros. NSDecide.fsetdec.
Defined.
Lemma ns_disj_singleton: forall x A, ~ NS.In x A -> NS.Empty (({·x·}) ⩀ A).
Proof.
  intros. NSDecide.fsetdec.
Defined.
Lemma ns_disj_add: forall A y C, NS.Empty (A ⩀ C) -> ~NS.In y C -> NS.Empty ((A ⨥ y) ⩀ C).
Proof.
  intros. NSDecide.fsetdec.
Defined.
Lemma ns_disj_union: forall A B C, NS.Empty (A ⩀ C) -> NS.Empty (B ⩀ C) -> NS.Empty ((A ⊍ B) ⩀ C).
Proof.
  intros. NSDecide.fsetdec.
Defined.



Global Hint Resolve ns_notin_empty : nsdb.
Global Hint Resolve ns_notin_union : nsdb.
Global Hint Resolve ns_notin_singleton : nsdb.
Global Hint Resolve ns_notin_add : nsdb.
Global Hint Resolve ns_disj_empty : nsdb.
Global Hint Resolve ns_disj_singleton : nsdb.
Global Hint Resolve ns_disj_union : nsdb.
Global Hint Resolve ns_disj_add : nsdb.



Definition classname := nat.
Definition fieldname  := nat.
Definition methodname := nat.
Definition pname := nat.
Definition fname := nat.
Definition ebop := nat. 
Definition euop := nat. 
Definition bop := nat. 
Definition buop := nat. 

Definition nullclass:classname := 0.
Definition Object:classname := 1.
Definition Facter:classname := 2.
Definition Pizza: classname := 3.
Definition Anchovy:classname := 4.
Definition fact: methodname := 0.
Definition price: methodname := 1.
Definition f1: fieldname := 0.
Definition reprnat: fieldname := 1.
Definition next: fieldname := 2.
Definition repr: fieldname := 3.
Definition valid:pname := 0.
Definition valid2:pname := 1.
Definition valid':pname := 2.
Definition length:fname := 0.
Definition mainb: pname := 2.
Definition maine: fname := 2.

Definition ptr := (nat*classname)%type.

Global Hint Unfold next : namesdb.
Global Hint Unfold repr : namesdb.

Definition minus : ebop := 0.
Definition add : ebop := 1.
Definition union : ebop := 2.

Definition singleton : euop := 0.

Definition iptr : buop := 0.

Definition nlt: bop := 0.
Definition setdis: bop := 1.
Definition setsub: bop := 2.
Definition setin: bop := 3.

Notation "`+" := add.
Notation "`-" := minus.
Notation "`∪" := union.

Notation "`{}`" := singleton.

Notation "`⊂" := setsub.
Notation "`∈" := setin.
Notation "`<" := nlt.
Notation "`!!" := setdis.



Definition ffff {A: Type}(b: bool) (fff1: forall (pf: b = true), A) (fff2: forall (pf: b = false), A): A:= 
(((match b as b' return forall (pf:b = b'), A with 
    | true  => fun pf => fff1 pf 
    | false => fun pf => fff2 pf
    end) erefl)).

Lemma ffffelim': forall A b fff1 fff2 (a:A), ffff b fff1 fff2 = a -> (exists (ee: b = true), fff1 ee = a) \/ (exists (ee: b = false), fff2 ee = a).
Proof.
  intros. unfold ffff in  H. 
  destruct b;auto.
  left. exists erefl. auto.
  right. exists erefl. auto.
Defined.
Lemma ffffintro': forall A b (fff1:b = true -> A) (fff2:b = false -> A) (a:A), ((exists (ee: b = true), fff1 ee = a) \/ (exists (ee: b = false), fff2 ee = a)) -> ffff b fff1 fff2 = a.
Proof.
  intros.
  unfold ffff.
  destruct H;auto.

  destruct H as [ee H].
  destruct b. 
  assert (erefl = ee). apply eq_irrelevance. subst. auto.
  inversion ee. 

  destruct H as [ee H].
  destruct b.
  inversion ee.
  assert (erefl = ee). apply eq_irrelevance. subst. auto.
Defined.
Lemma ffffintro: forall A b (fff1:b = true -> A) (fff2:b = false -> A) (pf: b=true), ffff b fff1 fff2 = fff1 pf.
Proof.
  intros.
  unfold ffff.
  destruct b. 
  assert (erefl = pf). apply eq_irrelevance. subst. auto.
  inversion pf. 
Defined.
Lemma ffffintrof: forall A b (fff1:b = true -> A) (fff2:b = false -> A) (pf: b=false), ffff b fff1 fff2 = fff2 pf.
Proof.
  intros.
  unfold ffff.
  destruct b.  
  inversion pf. 
  assert (erefl = pf). apply eq_irrelevance. subst. auto.
Defined.

Inductive val :=
| vint :> nat -> val
| vptr :> ptr -> val
| vset :> PS.t -> val 
.
Definition pnull := ((0, nullclass) : ptr).

Definition typeof (v: val) := match v with| vptr (addr, cls) => cls  | _ => nullclass  end.

Definition null :val := vptr pnull.

Definition val_to_int  (v:val) := match v with vint v => v  | _ => 0 end.
Definition val_to_ptr  (v:val) := match v with vptr p => p  | _ => pnull end.
Definition val_to_set  (v:val) := match v with vset p => p  | _ => PS.empty end.
Notation "↓ₚ v" := (val_to_ptr v) (at level 40).
Notation "↓ₛ v" := (val_to_set v) (at level 40).

Definition veq a b := 
  match a with 
  | vint n => match b with | vint m => Nat.eqb n m | _ => false end
  | vptr p => match b with | vptr q => if natnat_DT.eq_dec p q then true else false | _ => false end
  | vset s1 => match b with | vset s2 => PS.equal s1 s2 | _ => false end
  end.
Lemma veqsym: forall a b, veq a b -> veq b a.
Admitted.
Lemma veqtrans: forall a b c, veq a b -> veq b c -> veq a c.
Admitted.
Lemma veqseq: forall a b, veq a b -> PS.equal (↓ₛ a) (↓ₛ b).
Admitted.
Lemma veqpeq: forall a b, veq a b -> (↓ₚ a) = (↓ₚ b).
Admitted.
Lemma veqrefl: forall a, veq a a. Admitted.
Lemma veqf: forall a b s (f:fieldname), veq a b -> veq (s ((val_to_ptr a), f)) (s ((val_to_ptr b), f)). Admitted.


Notation "v1 `= v2" := (veq v1 v2) (at level 40).
Definition isptr (v:val) := match v with vint v => false | _ => true end.

Definition liftsub x y := Nat.sub (val_to_int x) (val_to_int y).
Definition liftadd x y := Nat.add (val_to_int x) (val_to_int y).
Definition liftsing x := (PS.add (val_to_ptr x) PS.empty).
Definition liftunion x y := PS.union (val_to_set x) (val_to_set y).
Definition liftlt x y := Nat.ltb (val_to_int x) (val_to_int y).
Definition liftin x y := PS.mem (val_to_ptr x) (val_to_set y).

Definition liftsubset x y := compssubset (val_to_set x) (val_to_set y).

Definition reduce (s: PNS.t): PS.t := ⌊'' fun loc ps => PS.add loc.1 ps ''⌋ s ▹ PS.empty. 
(* Definition liftdisjoint x y := PNS.equal (PNS.inter (expand (val_to_set x)) (expand (val_to_set y))) PNS.empty. *)
Definition liftdisjoint x y := PS.is_empty (PS.inter ( (val_to_set x)) ( (val_to_set y))).

Definition bops: bop -> (val -> val -> bool) := fun op => 
if Nat.eq_dec op nlt then liftlt else 
if Nat.eq_dec op setdis then liftdisjoint else 
if Nat.eq_dec op setsub then liftsubset else 
if Nat.eq_dec op setin then liftin else 
(fun x y => true).
Definition ebops: ebop -> (val -> val -> val) := fun eop => 
if Nat.eq_dec eop minus then liftsub else 
if Nat.eq_dec eop add then liftadd else
if Nat.eq_dec eop union then liftunion else
(fun x y => x).
Definition euops: euop -> (val -> val) := fun eop => 
if Nat.eq_dec eop singleton then liftsing 
else (fun x => x).
Definition buops: bop -> (val -> bool) := fun op => 
if Nat.eq_dec op iptr then isptr else 
(fun x => true).
Ltac handle_bops :=
repeat (match goal with
| [H: is_true (bops ?op ?A ?B) |- _ ] =>
  autounfold with dbops in H; simpl in H
| [H: (bops ?op ?A ?B) = false|- _ ] =>
  autounfold with dbops in H; simpl in H
| [H: (bops ?op ?A ?B) = true|- _ ] =>
  autounfold with dbops in H; simpl in H
| [ |- is_true (bops ?op ?A ?B) ] =>
  autounfold with dbops; simpl
| [ |- (bops ?op ?A ?B) = false ] =>
  autounfold with dbops; simpl
| [ |- (bops ?op ?A ?B) = true ] =>
  autounfold with dbops; simpl
end).

Lemma ebopmorphism: forall v1 v2 v op, veq v1 v2 -> veq (ebops op v1 v) (ebops op v2 v).
Admitted.
Lemma ebopmorphism': forall v1 v2 v op, veq v1 v2 -> veq (ebops op v v1) (ebops op v v2).
Admitted.
Lemma ebopmorphism'': forall v1 v2 v1' v2' op, veq v1 v2 -> veq v1' v2' -> veq (ebops op v1' v1) (ebops op v2' v2).
Admitted.

Lemma euopmorphism'': forall v1 v2 op, veq v1 v2 -> veq (euops op v1) (euops op  v2).
Admitted.

Lemma famorphism: forall v1 v2 h1 h2 (f:fieldname), veq v1 v2 -> veq (h1 (↓ₚ v1, f)) (h2 (↓ₚ v1, f)) -> veq (h1 (↓ₚ v1, f)) (h2 (↓ₚ v2, f)).
  intros. apply veqpeq in H.  rewrite <- H. auto.
Qed.
Lemma bopmorphism: forall v1 v2 v op, veq v1 v2 -> (bops op v v1) = (bops op v v2).
Admitted.
Lemma bopmorphism': forall v1 v2 v op, veq v1 v2 -> (bops op v1 v) = (bops op v2 v).
Admitted.
Lemma bopmorphism'': forall v1 v2 v1' v2' op, veq v1 v2 -> veq v1' v2' -> (bops op v1 v1') = (bops op v2 v2').
Admitted.

Lemma buopmorphism: forall v1 v2 op, veq v1 v2 -> (buops op v1) = (buops op v2).
Admitted.


Lemma in_singleton: forall v r, bops `∈ v (euops `{}` r) = veq v r.
Admitted.

(* Lemma in_union  *)
Lemma notin_union: forall v s1 s2, bops `∈ v (s1) = false -> bops `∈ v (s2) = false -> bops `∈ v (ebops `∪ s1 s2) = false.
Admitted.
Lemma veqmorphism: forall v1 v1' v2 v2', veq v1 v1' -> veq v2 v2' -> veq v1 v2 = veq v1' v2'.
Admitted.

Definition stack := var -> val.                 (* finite map var  → val   *)
Definition heap  := (ptr * fieldname) -> val.              (* finite map addr → obj   *)
(*we don't alias sets now*)
(* Definition aset := PS.t.
Definition ftptset := PNS.t.  *)
Definition state := prod (prod stack heap) PS.t. 

Definition exeassn := state -> bool.
Definition teassn: exeassn := fun s => true.
Definition expr := state -> val.

Definition var_expr (x: var) : expr := (fun s => (fst (fst s)) x).
Definition lift0 (v: val) : expr := fun s => v.

Definition substlist := list (var * val).
Fixpoint substl (s: stack) (subs: substlist) : stack :=
  match subs with
  | nil => fun x' => s x'
  | (x,e) :: subs' => fun x' => 
      if Nat.eq_dec x' x then e else (substl s subs') x'
  end.

Fixpoint substl_trunc (subs: substlist) : stack :=
  match subs with
  | nil => fun _ => null
  | (x,e) :: subs' => fun x' => 
      if Nat.eqb x' x then e else substl_trunc subs' x'
  end.

Definition state_trunc (s: state) (subs: substlist) : state :=
  (substl_trunc subs, snd (fst s), snd s).

Definition state_substl (s: state) (subs: substlist) : state :=
  (substl s.1.1 subs, snd (fst s), snd s).

Global Notation "s [{`! sub !`}]" := ((state_trunc s sub)) (at level 8, sub at level 40, format "s [{`! sub !`}]").
Global Notation "s [{`` sub ``}]" := ((state_substl s sub)) (at level 8, sub at level 40, format "s [{`` sub ``}]").

From Equations Require Import Equations.
Require Import Lia.


Inductive exprd:Type:= 
| evar: var -> exprd
| efield: exprd -> fieldname -> exprd
| eval: val -> exprd 
| efunc: forall c, c <> Object -> exprd -> fname -> exprd
| eite: dbexp -> exprd -> exprd -> exprd
| b': exprd -> ebop -> exprd -> exprd
| u': euop -> exprd -> exprd
with dbexp: Type := 
(* | atom: exeassn -> dbexp *)
| dbc : bool -> dbexp 
| dbeq: exprd -> exprd -> dbexp 
| u_ : buop -> exprd -> dbexp
| b_: exprd -> bop -> exprd -> dbexp 
| dbsubclass: exprd -> classname -> dbexp
| dbacc: exprd -> dbexp 
| dbcall: forall c, c <> Object -> exprd -> pname -> dbexp
| dbnot: dbexp -> dbexp
| dbconj: dbexp -> dbexp -> dbexp
| dbsc: dbexp -> dbexp -> dbexp
| dbite: dbexp -> dbexp -> dbexp -> dbexp
| dbdecm: classname -> methodname -> state -> classname -> methodname -> var -> list var -> dbexp
.

Scheme expr_mutind  := Induction for exprd  Sort Prop
with   db_mutind  := Induction for dbexp  Sort Prop.
Combined Scheme syn_mutind from 
    expr_mutind, db_mutind.

Lemma fold_add_init: forall (f : NS.elt -> dbexp -> dbexp) i s x, ~NS.In x s -> (⌊ f ⌋ (NS.add x s) ▹ i) = (f x (⌊ f ⌋ s ▹ i)).
Proof.
  intros. apply NS'.fold_add;auto. admit. admit.
Admitted.

Lemma fold_equal_init: forall (f : NS.elt -> dbexp -> dbexp) i s s', NS.Equal s s' -> (⌊ f ⌋ s ▹ i) = (⌊ f ⌋ s' ▹ i).
Proof.
  intros. apply NS'.fold_equal;auto. admit. admit.
Admitted.



(*this left recursive pattern is tricky, better avoid it*)
Notation "  e … f " := (efield e f) (at level 40, left associativity).
Notation "  ′ x  " := (evar x) (at level 50, left associativity).
Notation "  ! x  " := (eval x) (at level 50, left associativity).
(* Definition testvar x f :=  (′ x) … f.
Lemma showtestvar: forall x f, (′ x) … f = (′ x) … f. *)
Notation " 'eif' test 'then' e1 'else' e2  " := (eite test e1 e2) (at level 40, left associativity).
Notation "  e # C ∥ n ⟼ p () " := (efunc C n e p) (at level 40, p at level 9, left associativity).
Notation "{ₛ e ₛ}" := (u' singleton e) (at level 40).
Definition setx x := {ₛ (′ x) ₛ}.
(* Variable funcname1: e1 op e2 *)

Notation "  e @ C ∥ n ⟼ p () " := (dbcall C n e p) (at level 40, p at level 9, left associativity).
Notation "P <*>· Q" := (dbsc P Q) (at level 38, right associativity).   
Notation "P </\>· Q" := (dbconj P Q) (at level 38, right associativity).   
Notation "<!> P" := (dbnot P) (at level 40).   
Notation "e1 ·=· e2" := (dbeq e1 e2) (at level 40).   
Notation " 'bif' test 'then' e1 'else' e2  " := (dbite test e1 e2) (at level 40, left associativity).
(* Notation "'+++' e1 '+++' op '+++' e2" := (b_ e1 op e2) (at level 40, left associativity).
Definition dd1 e1 op e2 := +++ e1 +++ op +++ e2. *)
Definition eqb_of_sumbool {A : Type} {a b : A} {P: A -> A -> Prop}(H : {P a b} + {~ P a b}) : bool :=
  match H with
  | left _ => true
  | right _ => false
  end.





(* Definition acc(e:exprd) (f:fieldname) : exeassn := framedE (efield e f). *)
(*considered not "deep" enough, e.g., a.f.g*)
(* Definition accd(e:expr) (f:fieldname) : exeassn := fun s => snd s (val_to_ptr (e s), f).  *)
Definition Not (t: exeassn): exeassn := (fun s => negb (t s)).
Definition Conj (a b: exeassn): exeassn:= fun s => (andb (a s) (b s)). 
Definition Disj (a b: exeassn): exeassn:= fun s => (orb (a s) (b s)). 
(* Definition Imp (a b: exeassn): Prop:= forall s, (implb (a s) (b s)) = true.  *)
Definition IMP (a b: state -> Prop): Prop:= forall s, a s -> b s. 
Notation "P ⩠ Q" := (Conj P Q) (at level 40).
Notation "P ⩣ Q" := (Disj P Q) (at level 40).



Require Import Coq.Classes.RelationClasses.  (* for StrictOrder *)

(*we take the handling of dbsc simple here*)
(* Fixpoint prfragb_(db: dbexp) (s:state):= 
  match db with 
  | dbc b => PNS.empty
  | dbeq e1 e2 => PNS.empty
  | dbacc e f => PNS.singleton (val_to_ptr ((⟦ e ⟧ϵ) (s)), f)
  | dbcall e D q => PNS.empty 
  | dbsc d1 d2 => PNS.union (prfragb_ d1 s) + (prfragb_ d2 s)
  | dbite e d1 d2 => if interpbbt (e s) then pfragb_ d1 s else pfragb_ d2 s
  end  *)
Definition pfrag(pf: PNS.t) (p: PS.t): bool := PS.subset (reduce pf) p.
Notation "p ◄ P" := (pfrag p P) (at level 40).  






Inductive cmd :=
| assign  : var -> exprd -> cmd
| skip    : cmd
| seq     : cmd -> cmd -> cmd
| cond    : dbexp -> cmd -> cmd -> cmd
| cread  :  var -> fieldname -> var -> cmd
| cwrite  : var -> fieldname -> exprd -> cmd
| calloc  : var -> classname -> cmd
| cdcall  : var -> var -> methodname -> list var -> cmd
.
(*ᵪ is for executation*)
Notation " 'cif' test 'then' '{ᵪ' c1 '}ᵪ' 'else' '{ᵪ' c2 '}ᵪ' " := (cond test c1 c2) (at level 40, left associativity).
Notation "c1 ;; c2" := (seq c1 c2) (at level 41, right associativity).
Notation "x `:= e " := (assign x e) (at level 40).
Notation "x `≕ y `… f " := (cread x f y) (at level 39, y at level 30). (*todo, why we need this y at level 30?*)
Notation "x `… f `:= e " := (cwrite x f e) (at level 39, f at level 39).
Notation "x `≔ C " := (calloc x C) (at level 40).
Notation "x `⩴ y ⟼ m (` es `) " := (cdcall x y m es) (at level 40).
Definition testcall x y m z := x `⩴ y ⟼ m (` [z;z] `).
Definition testread x y f := x `≕ y `… f.
Definition ff test x e := cif test then {ᵪ ret `:= e ;; x `:= e }ᵪ else {ᵪ x `:= e }ᵪ.
Definition gf x e := x `≔ e.
Definition fff x f y := x `… f `:= y.
Definition fffff e f := e … f.

Definition class := ((pname -> dbexp) * (fname -> exprd) * (methodname -> cmd) * NS.t * classname)%type.
Definition getp(c:class) (p:pname) := (fst (fst (fst (fst c)))) p.
Definition getfun(c:class) (f:fname) := (snd (fst (fst (fst c)))) f.
Definition getm(c:class) (m:methodname) := (snd (fst (fst c))) m.
Definition getf(c:class) := (snd (fst c)).
Definition getsuper(c:class) := (snd c).
Definition Program := classname -> class.

Definition dbt := dbc true.
Definition dbf := dbc false.
Global Notation "⊤" := dbt.
Global Notation "⊥" := dbf.

Definition emptyclass:class := ((fun p => dbt), (fun p => eval null), (fun m => skip), (NS.empty), Object).
Definition emptyspec := (fun (m:pname) => (dbt, dbt)).
Definition specTable := classname -> ((pname -> exprd) * (methodname -> (list var * dbexp * dbexp))).



(*----------Syntactic Operations: substitution and field substitution----------*)
Fixpoint synpure(e:exprd) :=
  match e with 
  | evar v => true
  | efield de1 f => false
  | eval vv => true
  | efunc D Dok e f => false
  | eite e e1 e2 => synpureb e && synpure e1 && synpure e2
  | b' e1 op e2 => synpure e1 && synpure e2
  | u' op e1 => synpure e1
  end
with
synpureb (db:dbexp) := 
  match db with 
  | dbc b => true
  | dbeq e1 e2 => (synpure e1) && (synpure e2) 
  | b_ e1 op e2 => (synpure e1) && (synpure e2) 
  | u_ op e1 => (synpure e1) 
  | dbacc e => (synpure e)
  | dbcall D Dok e q => (synpure e) 
  | dbsc d1 d2 => (synpureb d1) && (synpureb d2)
  | dbconj d1 d2 => (synpureb d1) && (synpureb d2)
  | dbnot d1 => synpureb d1
  | dbite e d1 d2 => (synpureb e) && ((synpureb d1) && (synpureb d2))
  | dbdecm C' p' sig D q y zs => false
  | dbsubclass e C => synpure e
end.

Definition pureexprd := {v: exprd| synpure v}.


Definition synsubst:= NM.t pureexprd.
Program Definition varpexpr (v:var) : pureexprd := exist _ (′ v) _.
Program Definition valpexpr (v:val) : pureexprd := exist _ (! v) _.
Fixpoint dsubstlist (e:exprd) (sub: synsubst): exprd :=
  match e with 
  | evar x' => match NM.find x' sub with | Some e' => sval e' | None => evar x' end
  | efield e1 f => efield (dsubstlist e1 sub) f
  | eval vv => eval vv 
  | efunc C Cok e f => efunc C Cok (dsubstlist e sub) f
  | eite test e1 e2 => eite  (dbsubstlist test sub) (dsubstlist e1 sub) (dsubstlist e2 sub)
  | b' e1 op e2 => b' (dsubstlist e1 sub) op (dsubstlist e2 sub)
  | u' op e1 => u' op (dsubstlist e1 sub)
  end
with dbsubstlist (g: dbexp) (sub: synsubst): dbexp :=
  match g with 
  | dbc b => dbc b 
  | dbeq e1 e2 => dbeq (dsubstlist e1 sub) (dsubstlist e2 sub) 
  | b_ e1 op e2 => b_ (dsubstlist e1 sub) op (dsubstlist e2 sub) 
  | u_ op e1 => u_ op (dsubstlist e1 sub)
  | dbacc e => dbacc (dsubstlist e sub)
  | dbcall D Dok e q => dbcall D Dok (dsubstlist e sub) q 
  | dbsc d1 d2 => dbsc (dbsubstlist d1 sub) (dbsubstlist d2 sub)
  | dbconj d1 d2 => dbconj (dbsubstlist d1 sub) (dbsubstlist d2 sub)
  | dbnot d1 => dbnot (dbsubstlist d1 sub)
  | dbite e d1 d2 => dbite (dbsubstlist e sub) (dbsubstlist d1 sub) (dbsubstlist d2 sub)
  | dbdecm C' p' sig D q y zs => g (*TODO: fixme*)
  | dbsubclass e C => g (*TODO: fixme*)
  end.
 


Fixpoint dsubst1f (e:exprd) (x:var) (f: fieldname) (y:var): exprd :=
  match e with 
  | evar x' => evar x' 
  | efield e1 f' => match e1 with | evar x' => if Nat.eq_dec x' x then if Nat.eq_dec f' f then evar y else efield (dsubst1f e1 x f y) f' else efield (dsubst1f e1 x f y) f'| _ => efield (dsubst1f e1 x f y) f' end
  | eval vv => eval vv 
  | efunc C Cok e f' => efunc C Cok (dsubst1f e x f y) f'
  | eite test e1 e2 => eite (dbsubst1f test x f y) (dsubst1f  e1 x f y) (dsubst1f e2 x f y) 
  | b' e1 op e2 => b' (dsubst1f  e1 x f y) op (dsubst1f  e2 x f y) 
  | u' op e1 => u' op (dsubst1f  e1 x f y) 
  end
with dbsubst1f (g: dbexp) (x:var) (f: fieldname) (y:var): dbexp :=
  match g with 
  | dbc b => dbc b 
  | dbeq e1 e2 => dbeq (dsubst1f e1 x f y) (dsubst1f e2 x f y) 
  | b_ e1 op e2 => b_ (dsubst1f  e1 x f y) op (dsubst1f e2 x f y) 
  | u_ op e1 => u_ op (dsubst1f e1 x f y)
  | dbacc e => dbacc (dsubst1f e x f y)
  | dbcall D Dok e q => dbcall D Dok (dsubst1f e x f y) q 
  | dbsc d1 d2 => dbsc (dbsubst1f d1 x f y) (dbsubst1f d2 x f y)
  | dbconj d1 d2 => dbconj (dbsubst1f d1 x f y) (dbsubst1f d2 x f y)
  | dbnot d1 => dbnot (dbsubst1f d1 x f y)
  | dbite e d1 d2 => dbite (dbsubst1f e x f y) (dbsubst1f d1 x f y) (dbsubst1f d2 x f y)
  | dbdecm C' p' sig D q y zs => g (*TODO: fixme*)
  | dbsubclass e C => g (*TODO: fixme*)
  end. 

Notation "db {` sub `}β" := ((dbsubstlist db sub)) (at level 9).
Notation "e {` sub `}ϵ" := ((dsubstlist e sub)) (at level 9).

Definition list_set zs := (List.fold_left (fun s z => NS.add z s) zs NS.empty).

Fixpoint fve(e:exprd) :=
  match e with 
  | evar v => NS.singleton v
  | efield de1 f => fve (de1)
  | eval vv => NS.empty
  | efunc D Dok e f => fve (e)
  | eite e e1 e2 => NS.union (fv e) (NS.union (fve e1) (fve e2)) 
  | b' e1 op e2 => NS.union (fve (e1)) (fve (e2))
  | u' op e1 => (fve (e1))
  end
with
fv (db:dbexp): NS.t := 
  match db with 
  | dbc b => NS.empty 
  | dbeq e1 e2 => NS.union (fve e1) (fve e2) 
  | b_ e1 op e2 => NS.union (fve e1) (fve e2) 
  | u_ op e1 => (fve e1) 
  | dbacc e => (fve e)
  | dbcall D Dok e q => (fve e) 
  | dbsc d1 d2 => NS.union (fv d1) (fv d2)
  | dbconj d1 d2 => NS.union (fv d1) (fv d2)
  | dbnot d1 => fv d1
  | dbite e d1 d2 => NS.union (fv e) (NS.union (fv d1) (fv d2))
  | dbdecm C' p' sig D q y zs => NS.add y (list_set zs)
  | dbsubclass e C => fve e
  end.

Fixpoint modifies (c: cmd): NS.t:=
  match c with
  | assign x _    =>  NS.singleton x
  | skip          =>  NS.empty
  | seq c1 c2     => NS.union (modifies c1) (modifies c2)
  | cond _ c1 c2    => NS.union (modifies c1) (modifies c2)
  | cwrite _ _ _   => NS.empty
  | cread x _ _    => NS.singleton x
  | calloc x _     => NS.add alloc (NS.singleton x)
  | cdcall x _ _ _ => NS.add alloc (NS.singleton x)
  end.

Definition getstack (s:state):= fst (fst s).
Definition getstack' {P} (s:{v:state|P v}):= ((proj1_sig s).1.1).
Definition getheap (s:state):= snd (fst s).
Definition getheap' {P} (s:{v:state|P v}):= ((proj1_sig s).1.2).
Notation " γ` x " := (getstack x) (at level 40).
Notation " Γ` x " := (getstack' x) (at level 40).
Notation " σ` x " := (getheap x) (at level 40).
Notation " Σ` x " := (getheap' x) (at level 40).

Definition updfield'(h: heap) (p:ptr) (f:fieldname) (vv:val) := (fun k => if (PNS.E.eq_dec ((p), f) k) then vv else h k).

Definition updfield(s: state) (var:var) (f:fieldname) (vv:val):state := 
let v := s.1.1 var in (γ` s, updfield' (σ` s) (val_to_ptr v) f vv, snd s).

Definition readfield'(h: heap) (p:ptr) (f:fieldname) := h (p, f).
Definition readfield (s: state) (var:var) (f:fieldname) := 
let v := (γ` s) var in 
match v with 
| vptr p => (readfield' (σ` s) p f)
| _ =>  (readfield' (σ` s) pnull f) 
end.
Definition readvar (s: state) (var:var) := if Nat.eq_dec var alloc then vset s.2 else (fst (fst s)) var.
Notation "s [` x · f `] " := (readfield s x f) (at level 39, x at level 39, f at level 39).
Notation "s [`` x · f ↦ v ``] " := (updfield s x f v) (at level 38).

Record dec_strorder : Type := {
  dso_T      :> Type ;
  dso_ltb     : dso_T -> dso_T -> bool ;
}.
Module Type Measures.
Parameter gamma: Program.
Parameter specs: specTable.
Parameter mford: dec_strorder.
Parameter mf: forall (p : classname * fname * state), mford.
Definition call_ordere := (fun x y : classname * fname * state => (dso_ltb mford (mf x) (mf y))).
Parameter wfe: well_founded call_ordere.

Parameter mdbord: dec_strorder.
Parameter m: forall (p : classname * fname * state), mdbord.
Definition call_order := (fun x y : classname * fname * state => (dso_ltb mdbord (m x) (m y))).
Parameter wfm:  well_founded call_order.
Notation " a <?β b " := (dso_ltb mdbord a b) (at level 30). 

Parameter mmethod: dec_strorder.
Parameter mm: forall (p : classname * methodname * state), mmethod.
Definition call_orderm := (fun x y : classname * methodname * state => (dso_ltb mmethod (mm x) (mm y))).
Parameter wfmm:  well_founded call_orderm.

End Measures.



Module BTSems (L : Measures).
Import L.

Definition pre C q := (((specs C).2 q).1.2).
Definition post C q := (((specs C).2 q).2).
Definition argsl C q := (((specs C).2 q).1.1).
(* Definition argsl C q := NS.elements (((specs C).2 q).1.1). *)

Definition expand (s: PS.t): PNS.t := ⌊' fun ptr pns => (⌊ (fun f pp => PNS.add (ptr, f) pp) ⌋  (getf (gamma (ptr.2))) ▹ pns) '⌋ s ▹ PNS.empty.

Fixpoint interpebt (de:exprd) (s:state) : val := 
  match de with 
  | evar v => readvar s v
  | efield de1 f => (snd(fst s)) (val_to_ptr (interpebt de1 s), f) 
  | eval v => v
  | efunc C Cok e f => null 
  | eite test e1 e2 => if interpbbt test s then interpebt e1 s else interpebt e2 s
  | b' e1 op e2 => ebops op (interpebt e1 s) (interpebt e2 s)
  | u' op e1 => euops op (interpebt e1 s)
  end
with interpbbt (db: dbexp) (s:state): bool:= 
match db with 
| dbc b => b 
| dbeq e1 e2 => veq (interpebt e1 s) ( (interpebt e2 s))
| b_ e1 op e2 => (((bops op) ((interpebt e1) ( s)) ((interpebt e2) ( s)))) 
| u_ op e1 => (((buops op) ((interpebt e1) ( s)) )) 
| dbsubclass e C => Nat.eqb (val_to_ptr (interpebt e s)).2 C
| dbacc e => true
| dbcall D dok e q => false 
| dbsc d1 d2 => false (*condition can't contain sc, this helps define sem first then pfrag, don't know if worth relexing.  *)
| dbconj d1 d2 => (interpbbt d1 s) && (interpbbt d2 s)
| dbnot d => negb (interpbbt d s)
| dbite e d1 d2 => if interpbbt e s then interpbbt d1 s else interpbbt d2 s
| dbdecm C p sig D q y zs => (dso_ltb mmethod (mm (D, q, s [{`! (this, s.1.1 y) :: (combine (argsl D q) (map s.1.1 zs)) !`}])) (mm (C, p, sig)))
end.
Global Notation "⟦ e ⟧ϵ" := (interpebt e) (at level 40). 
Global Notation "⟦ b ⟧β" := (interpbbt b) (at level 40). 

Fixpoint pfragebt (e: exprd)(s: state): PNS.t := 
match e with 
|(evar v) => PNS.empty
|(eval v) => PNS.empty
|(efield e f) => PNS.union (PNS.singleton (val_to_ptr (interpebt e s), f)) (pfragebt e s)
|(b' e1 op e2) => PNS.union (pfragebt e1 s) (pfragebt e2 s)
|(u' op e1) => (pfragebt e1 s)
|(efunc D Dok e g) => PNS.empty
|(eite e e1 e2) => (if (⟦e⟧β s) then (pfragebt e1 s) else (pfragebt e2 s)) ⋓ (pfragbbt e s)
end
with pfragbbt(db: dbexp) (s:state):= 
match db with 
| dbc b => PNS.empty
| dbeq e1 e2 => PNS.union (((pfragebt e1 ) ( s)))  (((pfragebt e2 ) ( s)))
| b_ e1 op e2 => PNS.union (((pfragebt e1 ) ( s)))  (((pfragebt e2 ) ( s)))
| u_ op e1 => (((pfragebt e1 ) ( s)))
| dbacc e => (((pfragebt e ) ( s)))  
| dbcall D Dok e q => PNS.empty 
| dbsc d1 d2 => PNS.union (pfragbbt d1 s)  (pfragbbt d2 s)
| dbconj d1 d2 => PNS.union (pfragbbt d1 s)  (pfragbbt d2 s)
| dbnot d1 => (pfragbbt d1 s)
| dbite e d1 d2 => (if interpbbt e s then pfragbbt d1 s else pfragbbt d2 s) ⋓ (pfragbbt e s)
| dbdecm C p sig D q y zs => PNS.empty 
| dbsubclass e C => (((pfragebt e ) ( s)))
end . 
Global Notation "⥙ e ⥕ϵ" := (pfragebt e) (at level 40). 
Global Notation "⥙ e ⥕β" := (pfragbbt e) (at level 40). 
Fixpoint wlpe (C:classname) (p:fname) (sig:state) (e: exprd) {struct e}: exeassn := 
  match e with 
  | evar v => teassn
  | eval v => teassn
  | efield e f => wlpe C p sig e 
  | efunc D Dok e f => (fun s => (dso_ltb mford (mf (D, f, (s[{`! [(this, ⟦e⟧ϵ s)] !`}]))) (mf (C, p, sig))))
  | eite e d1 d2 => Disj (Conj ( interpbbt e ) (wlpe C p sig d1)) (Conj (Not (⟦ e ⟧β)) (wlpe C p sig d2))
  | b' e1 op e2 => Conj (wlpe C p sig e1) (wlpe C p sig e2)
  | u' op e1 => (wlpe C p sig e1)
  end .
End BTSems.

Module Type PWF (L: Measures).
Module M := BTSems L.
Import M.
Import L.
Parameter faa': forall C p (s: state), (wlpe C p (s) (getfun (gamma C) p)) (s).
Parameter mainfreee: forall c sig, (wlpe Object maine sig c) sig.
End PWF.

Module ExprSems (L : Measures) (L2: PWF L).
Module M := BTSems L.
Import M.
Import L.
Import L2.

Transparent acc_A_B_lexprod .
Fixpoint sizee (e: exprd) : nat := 
  match e with 
  | evar v => 0
  | eval e => 0
  | efield e f => (sizee e) + 1
  | efunc C Cok e f => (sizee e) + 1
  | eite db e1 e2 => (sizee e1) + (sizee e2) + 1 
  | b' e1 op e2 => (sizee e1) + (sizee e2) + 1 
  | u' op e1 => (sizee e1) + 1 
  end. 

Definition eslt (e1 e2: exprd) := lt (sizee e1) (sizee e2).
Transparent well_founded_ltof.
Transparent wf_lexprod.
Lemma wfeslt: well_founded eslt.
  unfold eslt.
  apply well_founded_ltof. 
Defined.
Definition ordere := lexprod (classname * fname * state) exprd call_ordere eslt.

Lemma ordere_wf : WellFounded ordere.
Proof. apply wf_lexprod. apply L.wfe.  apply wfeslt.   Defined.

#[global] Hint Resolve ordere_wf : wf.
#[global] Instance ordere_WellFounded : WellFounded ordere
  := ordere_wf.

Fixpoint sizedb(db: dbexp) := 
  match db with 
  | dbc b => 0 
  | dbeq e1 e2 => 0
  | b_ e1 op e2 => 0
  | u_ op e1 => 0
  | dbacc e => 0 
  | dbcall D Dok e q => 0
  | dbsc d1 d2 => (sizedb d1) + (sizedb d2) + 1 
  | dbconj d1 d2 => (sizedb d1) + (sizedb d2) + 1 
  | dbnot d1 => (sizedb d1) + 1
  | dbite e d1 d2 => (sizedb e) + (sizedb d1) + (sizedb d2) + 1 
  | dbdecm C p sig D q y zs => 0
  | dbsubclass e C => 0
  end . 


Definition dbslt (d1 d2: dbexp) := lt (sizedb d1) (sizedb d2).
Lemma wfdbslt: well_founded dbslt.
  apply well_founded_ltof.
Defined.
Definition order := lexprod (classname * pname * state) dbexp call_order dbslt.
Transparent wf_lexprod.
Lemma order_wf : WellFounded order.
Proof. apply wf_lexprod. apply L.wfm.  apply wfdbslt.   Defined.

#[global] Hint Resolve order_wf : wf.
#[global] Instance order_WellFounded : WellFounded order
  := order_wf.


Program Definition strength1 {e d1 d2 s} (sp: (((e) ⩠ (d1)) ⩣ ((Not e) ⩠ (d2))) s) (pf: e s = true): ((d1)) s.
Proof.
  unfold Disj in sp. apply orb_true_iff in sp. destruct sp.
  auto. unfold Conj in H. apply andb_prop in H. destruct H;auto. 
  unfold Conj in H. apply andb_prop in H. destruct H. unfold Not in H. unfold negb in H. rewrite pf in H. inversion H.  (*why cann't just let pf be of es? *)
Defined.
Program Definition strength2 {e d1 d2 s}(sp: (((e) ⩠ (d1)) ⩣ ((Not e) ⩠ (d2))) s) (pf: e s = false): ((d2)) s.
Proof.
  unfold Disj in sp. apply orb_true_iff in sp. destruct sp.
  unfold Conj in H. apply andb_prop in H. destruct H. unfold Not in H. unfold negb in H. rewrite pf in H. inversion H.  
  auto. unfold Conj in H. apply andb_prop in H. destruct H;auto. 
Defined.
Program Definition split1' (E1 E2: exeassn) (ss: state) (H: (Conj E1 E2) ss = true): E1 ss.
  unfold Conj in H. apply andb_prop in H. destruct H. auto.
Defined.
Program Definition split2' (E1 E2: exeassn) (ss: state) (H: (Conj E1 E2) ss = true): E2 ss.
  unfold Conj in H. apply andb_prop in H. destruct H. auto.
Defined.
Global Notation "E ⨣ s" := (wlpe Object mainb s E) (at level 9, s at level 39).


Equations interpe C p (e: exprd)(s: state) (sp: (wlpe C p s e) s): val by wf ((C, p, s), e) ordere := 
interpe C p (evar v) s sp := readvar s v;
interpe C p (eval v) s sp := v;
interpe C p (efield de1 f) s sp := (snd(fst s)) (val_to_ptr (interpe C p de1 s sp), f);
interpe C p (b' e1 op e2) s sp := ebops op (interpe C p e1 s (split1' (wlpe C p s e1) (wlpe C p s e2) s sp)) (interpe C p e2 s (split2' (wlpe C p s e1) (wlpe C p s e2) s sp));
interpe C p (u' op e1) s sp := euops op (interpe C p e1 s sp );
interpe C p (efunc D Dok e g) s sp := interpe D g (getfun (L.gamma D) g)  (s[{`![(this, (⟦e⟧ϵ s))]!`}]) (faa' D g (s)[{`![(this, (⟦e⟧ϵ s))]!`}] );
interpe C p (eite e e1 e2) s sp := (@ffff val (⟦e⟧β s) (fun pf => interpe C p e1 s (@strength1 (⟦e⟧β) (wlpe C p s e1) (wlpe C p s e2) s sp pf) ) (fun pf => interpe C p e2 s (@strength2 (⟦e⟧β) (wlpe C p s e1) (wlpe C p s e2) s sp pf))).
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply left_lex. unfold call_ordere. assumption.
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.

Equations pfrage C p (e: exprd)(s: state) (sp: (wlpe C p s e) s): PNS.t by wf ((C, p, s), e) ordere := 
pfrage C p (evar v) s sp := PNS.empty;
pfrage C p (eval v) s sp := PNS.empty;
pfrage C p (efield e f) s sp := PNS.union (PNS.singleton (val_to_ptr (interpe C p e s sp), f)) (pfrage C p e s sp);
pfrage C p (b' e1 op e2) s sp := PNS.union (pfrage C p e1 s (split1' ((wlpe C p s e1)) ((wlpe C p s e2)) s sp)) (pfrage C p e2 s (split2' ((wlpe C p s e1)) ((wlpe C p s e2)) s sp));
pfrage C p (u' op e1) s sp := (pfrage C p e1 s sp);
pfrage C p (efunc D Dok e g) s sp := PNS.union (pfrage D g (getfun (L.gamma D) g) (s[{`![(this, (⟦e⟧ϵ s))]!`}]) (faa' D g (s)[{`![(this, (⟦e⟧ϵ s))]!`}])) (⥙e⥕ϵ s);
pfrage C p (eite e e1 e2) s sp := PNS.union ((@ffff PNS.t (⟦e⟧β s) (fun pf => pfrage C p e1 s (@strength1 (⟦e⟧β) (wlpe C p s e1) (wlpe C p s e2) s sp pf) ) (fun pf => pfrage C p e2 s (@strength2 (⟦e⟧β) (wlpe C p s e1) (wlpe C p s e2) s sp pf)))) ((⥙e⥕β s)).
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply left_lex. unfold call_ordere. assumption. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Next Obligation.
  apply right_lex. unfold eslt. simpl. lia. 
Defined.
Definition Interpe e := (fun s => interpe Object maine e s (mainfreee e s)).
Definition Pfrage e := (fun s => pfrage Object maine e s (mainfreee e s)).

Global Notation "⟦ e ⟧Ε" := (Interpe e) (at level 40). 
Global Notation "⥙ e ⥕Ε" := (Pfrage e) (at level 40).
Fixpoint wlpdb (C:classname) (p:pname) (sig:state) (db: dbexp) {struct db}: exeassn := 
  match db with 
  | dbc b => teassn 
  | dbeq e1 e2 => teassn
  | b_ e1 op e2 => teassn
  | u_ op e1 => teassn
  | dbacc e => teassn 
  | dbcall D Dok e q => (fun s => (m (D, q, (s[{`! [(this, ⟦e⟧Ε s)] !`}]))) <?β (m (C, p, sig)))
  | dbsc d1 d2 => Conj (wlpdb C p sig d1) (wlpdb C p sig d2)  
  | dbconj d1 d2 => Conj (wlpdb C p sig d1) (wlpdb C p sig d2)  
  | dbnot d1 => (wlpdb C p sig d1)
  | dbite e d1 d2 => Conj (wlpdb C p sig e) (Disj (Conj (⟦ e ⟧β) (wlpdb C p sig d1)) (Conj (Not (⟦ e ⟧β)) (wlpdb C p sig d2)))
  | dbdecm C p sig D q y zs => teassn
  | dbsubclass C e => teassn
  end .
End ExprSems.
Module Type PWF0 (L: Measures) (L0: PWF L).
Module MM := ExprSems L L0.
Import MM.M.
Import MM.
Import L.
Import L0.
Parameter mainfree: forall c sig, (wlpdb Object mainb sig c) sig.
Parameter directimp: forall C p s, (wlpdb C p s (getp (gamma C) p)) s.
Parameter alloc_fun: forall D g H, NS.mem alloc ((fve (getfun (gamma D) g)) ⨪ H) = false.
Parameter alloc_pred: forall D g H, NS.mem alloc ((fv (getp (gamma D) g)) ⨪ H) = false.
Parameter predfv: forall D g, ((fv (getp (gamma D) g))) ⊆ {·this·} .
Global Notation "P ⩲ s" := (wlpdb Object mainb s P) (at level 50, s at level 59).
End PWF0.

Module BTSemsHoare (L: Measures) (L0: PWF L) (L1: PWF0 L L0).
Import L.
Import L0.
Import L1.
Import L1.MM.M.
Import L1.MM.




Equations pfragb C p (db: dbexp)(s: state) (sp: (wlpdb C p s db) s): PNS.t by wf ((C, p, s), db) order := 
pfragb C p (dbc b) s sp := PNS.empty;
pfragb C p (dbeq e1 e2) s sp := PNS.union (((⥙ e1 ⥕Ε) ( s)))  (((⥙ e2 ⥕Ε) ( s)));
pfragb C p (b_ e1 op e2) s sp := PNS.union (((⥙ e1 ⥕Ε) ( s)))  (((⥙ e2 ⥕Ε) ( s)));
pfragb C p (u_ op  e1) s sp := (((⥙ e1 ⥕Ε) ( s)));
pfragb C p (dbacc e) s sp := ((⥙ e ⥕Ε) ( s));
pfragb C p (dbcall d dok e q) s sp:= PNS.union (pfragb d q (getp (gamma d) q)  (s[{`![(this, (⟦ e ⟧Ε s))]!`}]) (directimp d q (s)[{`![(this, (⟦ e ⟧Ε s))]!`}])) (((⥙ e ⥕Ε) ( s)));
pfragb C p (dbsc d1 d2) s sp:= PNS.union (pfragb C p d1 ( ( s )) ( (split1' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp)))
                                (pfragb C p d2 s ( (split2' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp)));
pfragb C p (dbconj d1 d2) s sp:= PNS.union (pfragb C p d1 (s) ( (split1' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp)))
                                (pfragb C p d2 ( s) ((split2' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp)));                        
pfragb C p (dbnot d1) s sp := (pfragb C p d1 s ((sp)) );
pfragb C p (dbite e d1 d2) s sp :=  PNS.union (@ffff PNS.t (⟦e⟧β s) (fun pf => pfragb C p d1 s (@strength1 (⟦e⟧β) (wlpdb C p s d1) (wlpdb C p s d2) s (split2' (wlpdb C p s e) ((((⟦e⟧β) ⩠ (wlpdb C p s d1)) ⩣ (Not (⟦e⟧β) ⩠ (wlpdb C p s d2)))) s sp) pf)) (fun pf => pfragb C p d2 s (@strength2 (⟦e⟧β) (wlpdb C p s d1) (wlpdb C p s d2) s (split2' (wlpdb C p s e) ((((⟦e⟧β) ⩠ (wlpdb C p s d1)) ⩣ (Not (⟦e⟧β) ⩠ (wlpdb C p s d2)))) s sp) pf))) (⥙e⥕β s);
pfragb C p (dbdecm C' p' sig D q y zs ) s sp := PNS.empty;
pfragb C p (dbsubclass e D) s sp := PNS.empty.

Next Obligation.
  unfold order. apply left_lex.
  unfold call_order.
  assumption.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia. 
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia. 
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia. 
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia. 
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia. 
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia. 
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia. 
Defined.
Definition psdisj A B := (PS.Empty (PS.inter A B)) .
Global Notation "A ! B" := (psdisj A B)(at level 5).
Definition pnsdisj A B := (PNS.is_empty (PNS.inter A B)) .
Global Notation "A !! B" := (pnsdisj A B)(at level 40).
Definition disjoint C p dP dQ (s:state) (Ps: wlpdb C p s dP s) (Qs: wlpdb C p s dQ s) := 
 ((pfragb C p dP (s) (Ps)) !! (pfragb C p dQ (s) (Qs))).

Notation "C - p ⥙ e ⥕Β" := (pfragb C p e) (at level 40). 
Definition Pfragb e := (fun s => (pfragb Object mainb e s (mainfree e s))).
Global Notation "⥙ e ⥕Β" := (Pfragb e) (at level 40). 

 
Equations interpb C p (db:dbexp)(s: state) (sp: wlpdb C p s db s): bool by wf ((C, p, s), db) order := 
interpb C p (dbc b) s sp  := b;
interpb C p (dbeq e1 e2) s sp := (veq ((⟦ e1 ⟧Ε) ( s)) ((⟦ e2 ⟧Ε) ( s))) ;
interpb C p (b_ e1 op e2) s sp := (bops op ( (⟦ e1 ⟧Ε s)) ( (⟦ e2 ⟧Ε s)));
interpb C p (u_ op e1) s sp := (buops op ( (⟦ e1 ⟧Ε s)));
interpb C p (dbacc e) s sp := true ;
interpb C p (dbcall D Dok e q) s sp := (interpb D q (getp (gamma D) q) (s[{`![(this, (⟦ e ⟧Ε s))]!`}])  (directimp D q ( s)[{`![(this, (⟦ e ⟧Ε s))]!`}]));
interpb C p (dbsc d1 d2) s sp :=
          (* andb (⥙ d1 ⥕Β s !! ⥙ d2 ⥕Β s) *)
          (disjoint C p d1 d2 s ( (split1' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp)) ( (split2' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp))) &&
          (interpb C p d1 ( (s )) ( (split1' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp))) &&
          (interpb C p d2 ( (s)) ( (split2' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp)));
interpb C p (dbconj d1 d2) s sp :=
          ((interpb C p d1 ( (s )) ( (split1' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp))) &&
          (interpb C p d2 ( (s)) ( (split2' ((wlpdb C p s d1)) ((wlpdb C p s d2)) s sp))));
interpb C p (dbnot d1) s sp := negb (interpb C p d1 s sp);
interpb C p (dbite e d1 d2) s sp := (@ffff bool (⟦e⟧β s) (fun pf => interpb C p d1 s (@strength1 (⟦e⟧β) (wlpdb C p s d1) (wlpdb C p s d2) s (split2' (wlpdb C p s e) ((((⟦e⟧β) ⩠ (wlpdb C p s d1)) ⩣ (Not (⟦e⟧β) ⩠ (wlpdb C p s d2)))) s sp) pf) ) (fun pf => interpb C p d2 s (@strength2 (⟦e⟧β) (wlpdb C p s d1) (wlpdb C p s d2) s (split2' (wlpdb C p s e) ((((⟦e⟧β) ⩠ (wlpdb C p s d1)) ⩣ (Not (⟦e⟧β) ⩠ (wlpdb C p s d2)))) s sp) pf)));
interpb C p (dbdecm C' p' sig D q y zs ) s sp := (dso_ltb mmethod (mm (D, q, s [{`! (this, s.1.1 y) :: (combine (argsl D q) (map s.1.1 zs)) !`}])) (mm (C', p', sig)));
interpb C p (dbsubclass e D) s sp := Nat.eqb (val_to_ptr (interpebt e s)).2 D.

Next Obligation.
  unfold order. apply left_lex.
  unfold call_order. 
  assumption.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia.
Defined.
Next Obligation.
  unfold order. apply right_lex. unfold dbslt. simpl. lia.
Defined.
Definition Interpb e := (fun s => (interpb Object mainb e s (mainfree e s))).
Global Notation "⟦ e ⟧Β" := (Interpb e) (at level 40). 

Definition dbsat e := fun s => (⟦ e ⟧Β s) && ((⥙ e ⥕Β s) ◄ s.2).
Global Notation "⟦ e ⟧𝚩" := (dbsat e)(at level 40). 
Definition DBImp d1 d2 := forall s, (implb ((⟦ d1 ⟧Β) s) ((⟦ d2 ⟧Β) s)) .
Notation "P ⇒ Q" := (DBImp P Q) (at level 40).
Definition dbIff P Q:= forall s, ⟦ P ⟧Β s = ⟦ Q ⟧Β s.
Notation "P ⇔ Q" := (dbIff P Q) (at level 30).
(* Definition Imp d1 d2 := forall s, andb (implb ((⟦ d1 ⟧Β) s) ((⟦ d2 ⟧Β) s)) (PNS.subset ((⥙ d2 ⥕Β) s) ((⥙ d1 ⥕Β) s)). *)
(*why implb is necessary: xx1=this.next -> |this.next.valid()| ⊆ |xx1.valid()| *)
(*why implb is necessary: 
ret in this.repr * this.valid() => acc ret.f

ret in this.repr -> |acc ret.f| ⊆ |this.valid()| *)

Definition Imp d1 d2 := forall s, (implb ((⟦ d1 ⟧Β) s) (((⟦ d2 ⟧Β) s) && (PNS.subset ((⥙ d2 ⥕Β) s) ((⥙ d1 ⥕Β) s)))) .
Notation "P ⟹ Q" := (Imp P Q) (at level 40).
Definition Iff d1 d2 := forall s, (Bool.eqb ((⟦ d1 ⟧Β) s) (((⟦ d2 ⟧Β) s) && (PNS.equal ((⥙ d2 ⥕Β) s) ((⥙ d1 ⥕Β) s)))).

Definition Iff2 d1 d2 := (Imp d1 d2) /\ (Imp d2 d1).
Notation "P ⟺ Q" := (Iff P Q) (at level 40).

Global Hint Rewrite pfragb_equation_1 : pfragb_db.
Global Hint Rewrite pfragb_equation_2 : pfragb_db.
Global Hint Rewrite pfragb_equation_3 : pfragb_db.
Global Hint Rewrite pfragb_equation_4 : pfragb_db.
Global Hint Rewrite pfragb_equation_5 : pfragb_db.
Global Hint Rewrite pfragb_equation_6 : pfragb_db.
(* Global Hint Rewrite pfragb_equation_7 : pfragb_db. *)
Global Hint Rewrite pfragb_equation_8 : pfragb_db.
Global Hint Rewrite pfragb_equation_9 : pfragb_db.
Global Hint Rewrite pfragb_equation_10 : pfragb_db.
(* Global Hint Rewrite pfragb_equation_11 : pfragb_db. *)
Global Hint Rewrite pfragb_equation_12 : pfragb_db.

Global Hint Rewrite interpb_equation_1 : interpb_db.
Global Hint Rewrite interpb_equation_2 : interpb_db.
Global Hint Rewrite interpb_equation_3 : interpb_db.
Global Hint Rewrite interpb_equation_4 : interpb_db.
Global Hint Rewrite interpb_equation_5 : interpb_db.
Global Hint Rewrite interpb_equation_6 : interpb_db.
Global Hint Rewrite interpb_equation_7 : interpb_db.
Global Hint Rewrite interpb_equation_8 : interpb_db.
Global Hint Rewrite interpb_equation_9 : interpb_db.
Global Hint Rewrite interpb_equation_10 : interpb_db.
(* Global Hint Rewrite interpb_equation_11 : interpb_db. *)
Global Hint Rewrite interpb_equation_12 : interpb_db.

Global Hint Unfold readvar : interpe.

Global Hint Unfold bops : dbops.
Global Hint Unfold liftin : dbops.
Global Hint Unfold liftsubset : dbops.
Global Hint Unfold liftdisjoint : dbops.
Global Hint Unfold compssubset : dbops.
Global Hint Unfold euops : dbops.
Global Hint Unfold ebops : dbops.
Global Hint Unfold liftsing : dbops.
Global Hint Unfold liftunion : dbops.

Ltac ibin H := unfold Interpb in H; autorewrite with interpb_db in H.
Ltac pbin H := unfold Pfragb in H; autorewrite with pfragb in H.
Ltac iein H := unfold Interpe in H; autorewrite with interpe in H.
Ltac pein H := unfold Pfrage in H; autorewrite with pfrage in H.

Ltac ib := unfold Interpb; autorewrite with interpb_db.
Ltac pb := unfold Pfragb; autorewrite with pfragb.
Ltac ie := unfold Interpe; autorewrite with interpe; autounfold with interpe.
Ltac pe := unfold Pfrage; autorewrite with pfrage.

Definition pure (db: dbexp) := forall s, PNS.Empty (⥙db⥕Β s). 
Definition pureexp (e: exprd) := forall c p s pf, (pfrage c p e s pf) = PNS.empty. 
Lemma pexprpure: forall (e: pureexprd), pureexp (sval e).
Admitted.
Lemma pexpr_interp: forall s2 xc2 xp2 (e:pureexprd) p2, (⟦ sval e ⟧ϵ) s2 = interpe xc2 xp2 (sval e) s2 p2 .
Admitted.


(*assign/read and nondep*)
Definition eqxcptS (f g: var -> val) (X: NS.t):=
  forall x, NS.mem x X -> (f x) = (g x).
(*write*)
Definition eqxcptH (f g: (ptr * fieldname) -> val) (X: PNS.t):=
  forall x, PNS.mem x X -> (f x) = (g x).
(*new*)
Definition eqxcptA (f g: PS.t) (X: PS.t):=
  forall x, PS.mem x X -> PS.mem x f = PS.mem x g.

Lemma exeqfsetsub: forall (s1 s2: stack) A B, NS.Subset B A -> eqxcptS s1 s2 A -> eqxcptS s1 s2 B.
Proof.
  intros.
  unfold eqxcptS in *.
  intros;apply H0.
  apply NS.mem_1. apply NS.mem_2 in H1.
  NSDecide.fsetdec.
Defined.
Lemma exeqhfsetsub: forall (s1 s2: heap) A B, PNS.Subset B A -> eqxcptH s1 s2 A -> eqxcptH s1 s2 B.
Proof.
  intros.
  unfold eqxcptH in *.
  intros;apply H0.
  apply PNS.mem_1. apply PNS.mem_2 in H1.
  PNSDecide.fsetdec.
Defined.

Lemma exeqpfsetsub: forall (s1 s2: PS.t) A B, PS.Subset B A -> eqxcptA s1 s2 A -> eqxcptA s1 s2 B.
Proof.
  intros.
  unfold eqxcptA in *.
  intros;apply H0.
  apply PS.mem_1. apply PS.mem_2 in H1.
  PSDecide.fsetdec.
Defined.

Lemma exeqrefl: forall (s1: stack) B, eqxcptS s1 s1 B.
Proof.
  intros.
  unfold eqxcptS in *. 
  intros;auto. 
Defined.
Lemma exeq_emp: forall s1 s2, eqxcptS s1 s2 ∅.
Proof.
  intros.
  unfold eqxcptS in *. 
  intros. apply NS.mem_2 in H. NSDecide.fsetdec. 
Defined.
Lemma exeqhrefl: forall (s1: heap) B, eqxcptH s1 s1 B.
Proof.
  intros.
  unfold eqxcptH in *.
  intros;auto. 
Defined.

Lemma exeqprefl: forall (s1: PS.t) B, eqxcptA s1 s1 B.
Proof.
  intros.
  unfold eqxcptA in *.
  intros;auto.
Defined.

Lemma exeqhempty: forall (s1 s2: heap) H, PNS.Empty H -> eqxcptH s1 s2 H.
intros. unfold eqxcptH. intros. apply PNS.mem_2 in H1. apply H0 in H1. contradiction.
Defined.

(*no requirement for the third component: partial on that, "Wrong", 
the third component is important to interpert "alloc"*)
Definition exeqFull (s1 s2:state) (FV: NS.t) (P: PNS.t):=
  eqxcptS s1.1.1 s2.1.1 FV /\ eqxcptH s1.1.2 s2.1.2 P. 
Definition state_resp_sub xs s2 (sub: synsubst) := forall v e, NM.find v sub = Some e -> readvar xs v = (⟦ sval e ⟧ϵ) s2.


Lemma exeqfull_sub: forall (s1 s2: state) A B C D, PNS.Subset B A -> NS.Subset D C -> exeqFull s1 s2 C A -> exeqFull s1 s2 D B.
Proof.
Admitted.

Ltac solve_exsub := eapply exeqfull_sub;eauto;[PNSDecide.fsetdec|NSDecide.fsetdec]. 

Lemma exeqfull_refl: forall s A B, exeqFull s s A B.
Admitted. 

Lemma exeqfull_sym: forall s1 s2 A B, exeqFull s1 s2 A B -> exeqFull s2 s1 A B.
Admitted. 

Lemma exeqsym: forall A B H, eqxcptS A B H -> eqxcptS B A H.
Admitted. 
Lemma exeqh_updf: forall (p: ptr) (f:fieldname) H h v, (PNS.singleton (p, f)) !! H -> eqxcptH h (updfield' h p f v) H.
Admitted.
(*P and Q have to be in Prop instead of in Type, otherwise cann't use this*)
Definition subsetcond {x A} (P Q:Prop)(aeq: (if NS.mem x A then P else Q))  A': NS.Subset A' A -> NS.mem x A' -> P.
  intros. case_eq(NS.mem x A);intros;auto. rewrite H1 in aeq. auto.
  assert (NS.mem x A). handle_sets. NSDecide.fsetdec. rewrite H2 in H1. inversion H1.
Defined. 
Ltac case_if :=
match goal with
| |- context[if ?b then _ else _] => case_eq b; intros; auto
end.
Ltac solve_fve e1 := 
  case_eq (NS.mem alloc (fve e1) );intros;auto;eapply (subsetcond) ;eauto; NSDecide.fsetdec. 
Ltac solve_fv e1 := 
  case_eq (NS.mem alloc (fv e1) );intros;auto;eapply (subsetcond) ;eauto; NSDecide.fsetdec. 
Ltac solve_ns ns := 
  case_eq (NS.mem alloc ns );intros;auto;eapply (subsetcond) ;eauto; NSDecide.fsetdec. 

Lemma in_split_l : forall A B (l:list (A*B)) (a:A),
    In a (fst (split l)) -> exists b, In (a, b) l .
Proof.
  intros A B l. induction l. 
  -
    intros. simpl in H. contradiction.
  -
    intros a0. destruct a as [a b]. intros. simpl in H. destruct (split l) as [left right]. simpl in H. destruct H.
    --
    exists b. simpl. left. rewrite H. auto.
    --
    apply IHl in H. destruct H. exists x. simpl. right. auto. 
Defined.
(*seems to be just the ordinal eq, but have to use this*)
Definition eqp A B:= (fun p p' : A * B =>
   p.1 = p'.1 /\ p.2 = p'.2).
Lemma inA_split_l : forall (l:list (nat*pureexprd)) (a:nat),
    InA eq a (fst (split l)) -> exists b, InA (NM.eq_key_elt (elt:=pureexprd)) (a, b) l .
Proof.
  intros l. induction l. 
  -
    intros. simpl in H. inversion H. 
  -
    intros a0. destruct a as [a b]. intros. simpl in H. destruct (split l) as [left right]. simpl in H. inversion H. (*must invert instead of destruct here*) subst y.
    --
    exists b. simpl. left. rewrite H1. unfold NM.eq_key_elt. unfold NM.Raw.PX.eqke. simpl. auto.
    --
    apply IHl in H1. destruct H1. exists x. simpl. right. auto. 
Defined.
Definition dom_nm (m: synsubst):= NS'.of_list (split (NM'.to_list m)).1.
Lemma nfind_nindom: forall v sub, NM.find (elt:=pureexprd) v sub = None -> (~ NS.In v (dom_nm sub)).
  intros.
  unfold dom_nm. intro in1. apply (proj1 (NS'.of_list_1 _ _)) in in1. 
  apply inA_split_l in in1. destruct in1. unfold NM'.to_list in H0. 
  apply NM.elements_2 in H0. apply NM.find_1 in H0. rewrite H in H0. inversion H0.
Defined.
Lemma nfind_indom: forall v sub e, NM.find (elt:=pureexprd) v sub = Some e -> (NS.In v (dom_nm sub)).
  intros.
  unfold dom_nm. apply (proj1 (NS'.of_list_1 _ _)). 
Admitted.

Lemma sembt_weakensub: 
(forall xe xs s2 sub xdsub (xds: xdsub = xe{`sub`}ϵ) (aeq: if NS.mem alloc ((fve xe) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fve xe) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragebt xe xs) -> state_resp_sub xs s2 sub -> 
(interpebt xe xs) = (interpebt xdsub s2)) /\
(forall xd xs s2 sub xdsub (xds: xdsub = xd{`sub`}β) (aeq: if NS.mem alloc ((fv xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fv xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragbbt xd xs) -> state_resp_sub xs s2 sub -> 
(interpbbt xd xs) = (interpbbt xdsub s2)).
apply syn_mutind;intros;subst xdsub.
  -
    simpl. case_eq(NM.find v sub);intros.
    --
    unfold state_resp_sub in H0.
    eapply H0;eauto.
    -- 
    simpl. ie. apply nfind_nindom in H1.  
    (*this is from right result of NM.find*)
    assert (NS.mem v (fve ( ′ v ) ⨪ dom_nm sub)). apply NS.mem_1. simpl. NSDecide.fsetdec.
    (*we can use the above if alloc = v, and get xs.2=s2.2*)
    case_eq(Nat.eq_dec v alloc);intros. rewrite <-e in aeq. rewrite H2 in aeq. f_equal. apply aeq.
    (*otherwise, we enhance mem with alloc and use exeq*)
    unfold exeqFull in H. destruct H. unfold eqxcptS in H. apply H. handle_sets. NSDecide.fsetdec. 
  -
    simpl.
    apply eq_trans with (s2.1.2 ((↓ₚ (⟦ e ⟧ϵ) xs, f))). (*is the other option possible?*)
    --
      unfold exeqFull in H0. destruct H0.  apply H2. simpl. apply PNS.mem_1. PNSDecide.fsetdec.
    --
      f_equal;auto. f_equal. f_equal. eapply H;auto. eapply exeqfull_sub;eauto. simpl. PNSDecide.fsetdec. simpl. NSDecide.fsetdec.
  -
    simpl. auto. 
  -
    intros. simpl. auto. 
  -
    intros. simpl. simpl in aeq.
    case_eq((⟦ d {` sub `}β⟧β) s2);intros.
    +
      simpl in H2.
      assert ((⟦ d ⟧β) xs = true).
      erewrite H;eauto. solve_ns (fv d ⨪ dom_nm sub). solve_exsub.
      rewrite H5.
      eapply H0;auto. 
      solve_ns ((fve e ⨪ dom_nm sub)). rewrite H5 in H2. solve_exsub.
    +
      simpl in H2.
      assert ((⟦ d ⟧β) xs = false).
      erewrite H;eauto. solve_ns ((fv d ⨪ dom_nm sub)). solve_exsub.
      rewrite H5.
      eapply H1;auto. 
      solve_ns ((fve e0 ⨪ dom_nm sub)). rewrite H5 in H2. solve_exsub.
  -
      intros. simpl. simpl in H1. simpl in aeq. f_equal. 
      eapply H;auto. solve_ns (fve e ⨪ dom_nm sub). solve_exsub.
      eapply H0;auto. solve_ns (fve e1 ⨪ dom_nm sub). solve_exsub.  
  -
      intros. simpl. simpl in H0. f_equal. 
      eapply H;auto. (*it seems that fsetdec knows how to handle non-union fvs*)
  -
    intros. simpl. auto.
  -
    intros. simpl.
    simpl in H1. simpl in aeq.
    f_equal.
    eapply H;auto. solve_ns (fve e ⨪ dom_nm sub). solve_exsub.
    eapply H0;auto. solve_ns (fve e0 ⨪ dom_nm sub). solve_exsub.
  -
    intros. simpl.
    simpl in H0.
    f_equal.  eapply H;auto. 
  -
    intros. simpl.
    simpl in H1. simpl in aeq.
    f_equal.
    eapply H;auto. solve_ns (fve e ⨪ dom_nm sub). solve_exsub.
    eapply H0;auto. solve_ns (fve e0 ⨪ dom_nm sub). solve_exsub.
  -
    intros. ib.
    admit.
  -
    intros. simpl; auto.
  -
    intros. simpl. auto.
  -
    intros. simpl in H0. simpl. erewrite H;eauto.
  -
    intros. simpl. simpl in H1. simpl in aeq.
    erewrite H;eauto. erewrite H0;eauto. 
    solve_ns (fv d0 ⨪ dom_nm sub). solve_exsub. solve_ns (fv d ⨪ dom_nm sub). solve_exsub. 
  -
    intros. simpl. auto.
  -
    intros. simpl. simpl in aeq. 
    case_eq((⟦ d {`sub `}β ⟧β) s2);intros.
    +
      simpl in H2.
      assert ((⟦ d ⟧β) xs = true). erewrite H;eauto. solve_ns (fv d ⨪ dom_nm sub). solve_exsub.
      rewrite H5.
      erewrite H0;eauto. solve_ns (fv d0 ⨪ dom_nm sub). rewrite H5 in H2. solve_exsub.
    +
      simpl in H2.
      assert ((⟦ d ⟧β) xs = false). erewrite H;eauto. solve_ns (fv d ⨪ dom_nm sub). solve_exsub.
      rewrite H5.
      erewrite H1;eauto. solve_ns (fv d1 ⨪ dom_nm sub). rewrite H5 in H2. solve_exsub.
  -
    intros. admit.

Admitted.
Lemma interpebt_weakensub: forall xe xs s2 sub xdsub (xds: xdsub = xe{`sub`}ϵ) (aeq: if NS.mem alloc ((fve xe) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fve xe) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragebt xe xs) -> state_resp_sub xs s2 sub -> 
(interpebt xe xs) = (interpebt xdsub s2).
apply sembt_weakensub.
Defined.
(*do we really have lebniz eq here?*)
Lemma pfragebt_weakensub: forall xe xs s2 sub xdsub (xds: xdsub = xe{`sub`}ϵ) (aeq: if NS.mem alloc ((fve xe) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fve xe) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragebt xe xs) -> state_resp_sub xs s2 sub -> 
(pfragebt xe xs) = (pfragebt xdsub s2).
Admitted.
Lemma interpbbt_weakensub: forall xd xs s2 sub xdsub (xds: xdsub = xd{`sub`}β) (aeq: if NS.mem alloc ((fv xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fv xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragbbt xd xs) -> state_resp_sub xs s2 sub -> 
(interpbbt xd xs) = (interpbbt xdsub s2).
apply sembt_weakensub.
Defined.
Lemma pfragbbt_weakensub: forall xd xs s2 sub xdsub (xds: xdsub = xd{`sub`}β)  (aeq: if NS.mem alloc ((fv xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fv xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragbbt xd xs) -> state_resp_sub xs s2 sub -> 
(pfragbbt xd xs) = (pfragbbt xd{`sub`}β s2).
Admitted.
Definition empsub := NM.empty pureexprd.
Lemma emp_sub_: (forall e, e = e{`empsub`}ϵ) /\ (forall db, db = db{`empsub`}β).
apply syn_mutind;intros;simpl; try congruence. (*can simply NM.find*)
Defined.
Lemma emp_sub: (forall e, e = e{`empsub`}ϵ) .
apply emp_sub_.
Defined.
Lemma emp_subb: forall db, db = db{`empsub`}β.
apply emp_sub_.
Defined.
Lemma emp_srs: forall s1 s2, state_resp_sub s1 s2 (empsub).
intros. unfold state_resp_sub. intros. apply NM.find_2 in H. apply NM.empty_1 in H. contradiction. 
Defined.
Global Hint Rewrite emp_sub: subdb.
Global Hint Rewrite emp_subb: subdb.
Global Hint Resolve emp_sub: subdb.
Global Hint Resolve emp_subb: subdb.
Global Hint Resolve emp_srs: subdb.
(*note that we don't need mutual induction here*)
Lemma interpe_weakensub: 
forall xc1 xp1 xd xs p1 xc2 xp2 s2 sub xdsub p2 (xds: xdsub = xd{`sub`}ϵ) (aeq: if NS.mem alloc ((fve xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fve xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfrage xc1 xp1 xd xs p1) -> state_resp_sub xs s2 sub -> 
(@interpe xc1 xp1 xd xs (p1)) = (@interpe xc2 xp2 xdsub s2 (p2)).
Proof.
  apply (@interpe_elim (fun (xc1 : classname) (xp1 : fname) (xd : exprd) (xs : state) (p1 : wlpe xc1 xp1 xs xd xs) res => 
  forall (xc2 : classname) (xp2 : fname) (s2 : state) sub xdsub p2 xds (aeq: if NS.mem alloc ((fve xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), exeqFull xs s2 ((fve xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfrage xc1 xp1 xd xs p1)-> state_resp_sub xs s2 sub -> res = (interpe xc2 xp2 xdsub s2 p2))).
  -
    intros.  
    case_eq(NM.find v sub);intros;simpl in xds; rewrite H1 in xds;subst xdsub.
    --
      simpl. eapply eq_trans. eapply H0;eauto. apply pexpr_interp. 
    --
      simpl. ie. apply nfind_nindom in H1.  
      assert (NS.mem v (fve ( ′ v ) ⨪ dom_nm sub)). apply NS.mem_1. simpl. NSDecide.fsetdec.
      case_eq(Nat.eq_dec v alloc);intros. rewrite <-e in aeq. rewrite H2 in aeq. f_equal. apply aeq. 
      unfold exeqFull in H. destruct H. unfold eqxcptS in H. apply H. handle_sets. NSDecide.fsetdec.  
  -
    intros.
    intros. subst xdsub. simpl. ie.
    
    simpl.
    apply eq_trans with (s2.1.2 ((↓ₚ (interpe C p de1 s sp), f))). (*is the other option possible?*)
    --
      unfold exeqFull in H0. destruct H0.  apply H2. simpl. apply PNS.mem_1. pe. ie. PNSDecide.fsetdec.
    --
      f_equal;auto. f_equal. f_equal. eapply H;auto. eapply exeqfull_sub;eauto. simpl. pe. PNSDecide.fsetdec. simpl. NSDecide.fsetdec.
  -
    intros. subst xdsub. simpl. ie. auto. 
  - 
    intros. subst xdsub. simpl. ie. eapply H;auto;simpl fve in *;auto. apply emp_sub. 
    rewrite alloc_fun. auto. unfold exeqFull. constructor. 
    --
    (*stack is changed*)
    unfold eqxcptS. intros. simpl. 
    case_eq(x =? this);intros. eapply interpebt_weakensub;eauto. eapply exeqfull_sub;eauto. pe. PNSDecide.fsetdec. simpl. NSDecide.fsetdec. auto. 
    --
    (*heap is structurally smaller*)
    simpl. unfold exeqFull in H0. destruct H0. pein H2. eapply exeqhfsetsub;eauto. PNSDecide.fsetdec.
    --
    apply emp_srs.
  -
    intros. subst xdsub. simpl. rewrite <- interpe_equation_5.  simpl in aeq.
    case_eq((⟦ e {`sub `}β ⟧β) s2);intros.
    +
      ie.
      assert ((⟦ e ⟧β) s = true). simpl in H1. erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). pein H1. solve_exsub.
      rewrite ffffintro with (pf:= H3). rewrite ffffintro with (pf:= H4).
      eapply H;auto. 
      solve_ns (fve e1 ⨪ dom_nm sub).
      simpl in H1. pein H1. rewrite ffffintro with (pf:= H4) in H1. solve_exsub.
    +
      ie.
      assert ((⟦ e ⟧β) s = false). simpl in H1. erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). pein H1. solve_exsub.
      rewrite ffffintrof with (pf:= H3). rewrite ffffintrof with (pf:= H4).
      eapply H0;auto.
      solve_ns (fve e2 ⨪ dom_nm sub).
      simpl in H1. pein H1. rewrite ffffintrof with (pf:= H4) in H1. solve_exsub.
  -
    intros. subst xdsub. simpl. ie. pein H1. simpl in H1. simpl in aeq. f_equal. 
    eapply H;auto. solve_ns (fve e1 ⨪ dom_nm sub). solve_exsub. 
    eapply H0;auto. solve_ns (fve e2 ⨪ dom_nm sub). solve_exsub. 
  -
    intros. subst xdsub. simpl. ie. pein H0. simpl in H0. f_equal. 
    eapply H;auto. (*it seems that fsetdec knows how to handle non-union fvs*)
Defined.
(*We should be able to remove this aeq constraint, pfrag is really constant on alloc...*)
Lemma pfrage_weakensub: forall xc1 xp1 xd xs p1 xc2 xp2 s2 sub xdsub p2 (xds: xdsub = xd{`sub`}ϵ) (aeq: if NS.mem alloc ((fve xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fve xd) ⨪ (dom_nm sub) ⨪ {·alloc·})(pfrage xc1 xp1 xd xs p1) -> state_resp_sub xs s2 sub -> 
@pfrage xc1 xp1 xd xs (p1) = @pfrage xc2 xp2 xdsub s2 (p2).
  apply (@pfrage_elim (fun (xc1 : classname) (xp1 : fname)  (xd : exprd) (xs : state) (p1 : wlpe xc1 xp1 xs xd xs) res => 
  forall (xc2 : classname) (xp2 : fname) (s2 : state) sub xdsub p2 (xds: xdsub = xd{`sub`}ϵ) (aeq: if NS.mem alloc ((fve xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), exeqFull xs s2 ((fve xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfrage xc1 xp1 xd xs p1) -> state_resp_sub xs s2 sub -> res = pfrage xc2 xp2 xdsub s2 p2));intros.
  -
    case_eq(NM.find v sub);intros;simpl in xds; rewrite H1 in xds;subst xdsub.
    --
      rewrite (pexprpure p0). auto.
    --
      pe. auto.
  -
    subst xdsub. simpl.
    pe. simpl in p2. simpl in H0. pein H0. simpl in aeq.
    assert ( (↓ₚ interpe C p e s sp) =  (↓ₚ interpe xc2 xp2 e {`sub `}ϵ s2 p2)) as HH. f_equal. eapply interpe_weakensub;auto. 
    solve_exsub.  rewrite HH.
    erewrite H;eauto. solve_exsub. 
  -
    subst xdsub. simpl. 
    rewrite pfrage_equation_3. auto.
  -
    subst xdsub. simpl. 
    pe. simpl in H0. pein H0. simpl in aeq.
    erewrite (H). Focus 2. apply emp_sub. 
    erewrite pfragebt_weakensub;eauto.
    solve_exsub.
    rewrite alloc_fun. auto. 
    unfold exeqFull. constructor.
    --
      unfold eqxcptS. intros. simpl.
      case_eq(x =? this);intros. eapply interpebt_weakensub;eauto. solve_exsub. auto. 
    --
    (*heap is structurally smaller*)
      simpl. unfold exeqFull in H0. destruct H0. pein H1. eapply exeqhfsetsub;eauto. PNSDecide.fsetdec.
    --
      apply emp_srs.
  -
    subst xdsub. simpl. 
    rewrite <- pfrage_equation_5. simpl in aeq.
    case_eq((⟦ e {`sub `}β ⟧β) s2);intros.
    +
      pe.  simpl in H1. pein H1.
      assert ((⟦ e ⟧β) s = true). erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub.
      rewrite ffffintro with (pf:= H3). rewrite ffffintro with (pf:= H4).
      erewrite H;eauto. erewrite pfragbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub.  solve_ns (fve e1 ⨪ dom_nm sub). rewrite ffffintro with (pf:= H4) in H1. solve_exsub.
    +
      pe.  simpl in H1. pein H1.
      assert ((⟦ e ⟧β) s = false). erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub.
      rewrite ffffintrof with (pf:= H3). rewrite ffffintrof with (pf:= H4).
      erewrite H0;eauto. erewrite pfragbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub. solve_ns (fve e2 ⨪ dom_nm sub). rewrite ffffintrof with (pf:= H4) in H1. solve_exsub.
  -
    subst xdsub. simpl. 
    pe. pein H1. simpl in H1. simpl in aeq. 
    (*have to manually specify, otherwise seems to have a bug*)
    erewrite H with (xdsub:=e1 {`sub `}ϵ);eauto.
    erewrite H0 with (xdsub := e2 {`sub `}ϵ);eauto. 

    solve_ns (fve e2 ⨪ dom_nm sub).
    solve_exsub.
    solve_ns (fve e1 ⨪ dom_nm sub).
    solve_exsub.
  -
    subst xdsub. simpl. 
    pe. pein H0. erewrite H with (xdsub:=e1 {`sub `}ϵ);eauto. 
Defined.

Lemma pfragb_weakensub: forall xc1 xp1 xd xs p1 xc2 xp2 s2 sub xdsub p2 (xds: xdsub = xd{`sub`}β) (aeq: if NS.mem alloc ((fv xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fv xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragb xc1 xp1 xd xs p1) -> state_resp_sub xs s2 sub -> 
@pfragb xc1 xp1 xd xs (p1) =  @pfragb xc2 xp2 xdsub s2 (p2).
  apply (@pfragb_elim (fun (xc1 : classname) (xp1 : fname) (xd : dbexp) (xs : state) p1 res => 
  forall (xc2 : classname) (xp2 : pname) (s2 : state) sub xdsub p2 (xds: xdsub = xd{`sub`}β) (aeq: if NS.mem alloc ((fv xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), exeqFull xs s2 ((fv xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) ((xc1 - xp1 ⥙ xd ⥕Β) xs p1) -> state_resp_sub xs s2 sub -> res = @pfragb xc2 xp2 xdsub s2 (p2)));intros; subst xdsub;simpl.
  -
    pb. auto.
  -
    intros. pb.
    simpl in H. pbin H. simpl in aeq.
    pe.
    erewrite pfrage_weakensub with (xd:=e1) (xdsub:=e1 {`sub `}ϵ);eauto. erewrite pfrage_weakensub with (xd:=e2) (xdsub:=e2 {`sub `}ϵ);eauto. solve_ns (fve e2 ⨪ dom_nm sub). solve_exsub. solve_ns (fve e1 ⨪ dom_nm sub). solve_exsub.
  -
    intros. pb.
    simpl in H. pbin H.
    pe.
    erewrite pfrage_weakensub;eauto.
  -
    intros. pb.
    simpl in H. pbin H. simpl in aeq.
    pe.
    erewrite pfrage_weakensub with (xd:=e1) (xdsub:=e1 {`sub `}ϵ);eauto. erewrite pfrage_weakensub with (xd:=e2);eauto. solve_ns (fve e2 ⨪ dom_nm sub). solve_exsub. solve_ns (fve e1 ⨪ dom_nm sub). solve_exsub.
  -
    intros. pb.
    admit.
  -
    intros. pb. pe. erewrite pfrage_weakensub with (xd:=e);eauto. simpl in H. pbin H. solve_exsub. 
  -
    intros. pb.
    simpl in H0. pbin H0. simpl in aeq.
    erewrite H. pe. erewrite pfrage_weakensub with (xd:=e);eauto. solve_exsub.
    apply emp_subb.
    rewrite alloc_pred. auto.
    unfold exeqFull. constructor.
    --
      unfold eqxcptS. intros. simpl.
      case_eq (x =? this);intros. eapply interpe_weakensub;eauto. solve_exsub. auto.
    --
      simpl. unfold exeqFull in H0. destruct H0. 
      eapply exeqhfsetsub;eauto. PNSDecide.fsetdec.
    --
      apply emp_srs.
  -
    intros. simpl in H0. pbin H0. pb. erewrite H with (xdsub := d1 {`sub `}β);eauto.
  -
    intros. pb. simpl in H1. pbin H1. simpl in aeq.
    erewrite H with (xdsub := d1 {`sub `}β);eauto. erewrite H0 with (xdsub := d2 {`sub `}β); eauto.
    solve_ns (fv d2 ⨪ dom_nm sub). solve_exsub. solve_ns (fv d1 ⨪ dom_nm sub). solve_exsub.
  -
    intros. pb. simpl in H1. pbin H1. simpl in aeq.
    erewrite H with (xdsub := d1 {`sub `}β);eauto. erewrite H0 with (xdsub := d2 {`sub `}β); eauto.
    solve_ns (fv d2 ⨪ dom_nm sub). solve_exsub. solve_ns (fv d1 ⨪ dom_nm sub). solve_exsub. 
  - 
    intros. rewrite <- pfragb_equation_11. simpl in aeq. 
    case_eq((⟦ e {`sub `}β ⟧β) s2);intros.
    +
      rewrite pfragb_equation_11. rewrite pfragb_equation_11. simpl in H1. pbin H1.
      assert ((⟦ e ⟧β) s = true). erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub.
      rewrite ffffintro with (pf:= H3). rewrite ffffintro with (pf:= H4).
      erewrite H;eauto. erewrite pfragbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub. solve_ns (fv d1 ⨪ dom_nm sub). rewrite ffffintro with (pf:= H4) in H1. solve_exsub.
    +
      rewrite pfragb_equation_11. rewrite pfragb_equation_11. simpl in H1. pbin H1.
      assert ((⟦ e ⟧β) s = false). erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub.
      rewrite ffffintrof with (pf:= H3). rewrite ffffintrof with (pf:= H4).
      erewrite H0;eauto. erewrite pfragbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub. solve_ns (fv d2 ⨪ dom_nm sub). rewrite ffffintrof with (pf:= H4) in H1. solve_exsub.
  -
    intros. admit.
Admitted.

Lemma interpb_weakensub: forall xc1 xp1 xd xs p1 xc2 xp2 s2 sub xdsub p2 (xds: xdsub = xd{`sub`}β) (aeq: if NS.mem alloc ((fv xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), 
exeqFull xs s2 ((fv xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) (pfragb xc1 xp1 xd xs p1) -> state_resp_sub xs s2 sub -> 
@interpb xc1 xp1 xd xs (p1) =  @interpb xc2 xp2 xdsub s2 (p2).
  apply (@interpb_elim (fun (xc1 : classname) (xp1 : fname) (xd : dbexp) (xs : state) p1 res => 
  forall (xc2 : classname) (xp2 : pname) (s2 : state) sub xdsub p2 (xds: xdsub = xd{`sub`}β) (aeq: if NS.mem alloc ((fv xd) ⨪ (dom_nm sub)) then xs.2 = s2.2 else True), exeqFull xs s2 ((fv xd) ⨪ (dom_nm sub) ⨪ {·alloc·}) ((xc1 - xp1 ⥙ xd ⥕Β) xs p1) -> state_resp_sub xs s2 sub -> res = interpb xc2 xp2 xdsub s2 p2));intros;subst xdsub;simpl.
  -
    intros. ib. auto.
  -
    intros. ib.
    simpl in H. pbin H. simpl in aeq.
    f_equal.
    eapply interpe_weakensub;eauto. solve_ns (fve e1 ⨪ dom_nm sub). solve_exsub.
    eapply interpe_weakensub;eauto. solve_ns (fve e2 ⨪ dom_nm sub). solve_exsub.
  -
    intros. ib.
    simpl in H. pbin H.
    f_equal. eapply interpe_weakensub;eauto. 
  -
    intros. ib.
    simpl in H. pbin H. simpl in aeq.
    f_equal.
    eapply interpe_weakensub;eauto. solve_ns (fve e1 ⨪ dom_nm sub). solve_exsub.
    eapply interpe_weakensub;eauto. solve_ns (fve e2 ⨪ dom_nm sub). solve_exsub.
  -
    intros. ib.
    admit.
  -
    intros. ib. auto.
  -
    intros. ib.
    simpl in H0. pbin H0. simpl in aeq.
    eapply H. 
    apply emp_subb.
    rewrite alloc_pred. auto.
    unfold exeqFull. constructor.
    --
      unfold eqxcptS. intros. simpl.
      case_eq (x =? this);intros. eapply interpe_weakensub;eauto. solve_exsub. auto. 
    --
      simpl. unfold exeqFull in H0. destruct H0. 
      eapply exeqhfsetsub;eauto. PNSDecide.fsetdec.
    --
      apply emp_srs.
  -
    intros. simpl in H0. pbin H0. ib. erewrite H;eauto. reflexivity.
  -
    intros. ib. simpl in H1. pbin H1. simpl in aeq.
    erewrite H with (xdsub:=d1 {`sub `}β);eauto. erewrite H0 with (xdsub:=d2 {`sub `}β); eauto.
    solve_ns (fv d2 ⨪ dom_nm sub). solve_exsub. solve_ns (fv d1 ⨪ dom_nm sub). solve_exsub.
  -
    intros. ib. simpl in H1. pbin H1. simpl in aeq.
    unfold disjoint.
    unfold pnsdisj. simpl. unfold Pfragb.
    erewrite pfragb_weakensub with (xd:=d1) (xdsub := d1 {` sub `}β);auto.
    erewrite pfragb_weakensub with (xd:=d2) (xdsub := d2 {` sub `}β);auto.
    erewrite H with (xdsub := d1 {` sub `}β);auto. erewrite H0 with (xdsub := d2 {` sub `}β);auto. 
    solve_ns (fv d2 ⨪ dom_nm sub). solve_exsub. solve_ns (fv d1 ⨪ dom_nm sub). solve_exsub. auto. solve_ns (fv d2 ⨪ dom_nm sub). solve_exsub. auto. solve_ns (fv d1 ⨪ dom_nm sub). solve_exsub. auto.  
  -
    intros. rewrite <- interpb_equation_11. simpl in aeq. 
    case_eq((⟦ e {`sub `}β ⟧β) s2);intros.
    +
      rewrite interpb_equation_11. rewrite interpb_equation_11. simpl in H1. pbin H1.
      assert ((⟦ e ⟧β) s = true). erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub.
      rewrite ffffintro with (pf:= H3). rewrite ffffintro with (pf:= H4).
      erewrite H;eauto. solve_ns (fv d1 ⨪ dom_nm sub). rewrite ffffintro with (pf:= H4) in H1. solve_exsub.
    +
      rewrite interpb_equation_11. rewrite interpb_equation_11. simpl in H1. pbin H1.
      assert ((⟦ e ⟧β) s = false). erewrite interpbbt_weakensub;eauto. solve_ns (fv e ⨪ dom_nm sub). solve_exsub.
      rewrite ffffintrof with (pf:= H3). rewrite ffffintrof with (pf:= H4).
      erewrite H0;eauto. solve_ns (fv d2 ⨪ dom_nm sub). rewrite ffffintrof with (pf:= H4) in H1. solve_exsub.
  -
    intros. admit.

Admitted.


(*those lemmas are so handy that they need a deep remark*)
Lemma interpb_nodepwp: forall d C p s p1 p2, interpb C p d s p1 = interpb C p d s p2.
intros. apply interpb_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto.
Defined.

Lemma interpb_nodepwp': forall d C p s p1, interpb C p d s p1 = ⟦d⟧Β s.
intros. unfold Interpb. apply interpb_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto. 
Defined.

Lemma pfragb_nodepwp: forall d C p s p1 p2, pfragb C p d s p1 = pfragb C p d s p2.
intros. apply pfragb_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto.
Defined.

Lemma pfragb_nodepwp': forall d C p s p1, pfragb C p d s p1 = ⥙d⥕Β s.
intros. apply pfragb_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto.
Defined.

Lemma interpe_nodepwp: forall d C p s p1 p2, interpe C p d s p1 = interpe C p d s p2.
intros. apply interpe_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto.
Defined.

Lemma interpe_nodepwp': forall d C p s p1, interpe C p d s p1 = ⟦d⟧Ε s.
intros. unfold Interpb. apply interpe_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto. 
Defined.

Lemma pfrage_nodepwp: forall d C p s p1 p2, pfrage C p d s p1 = pfrage C p d s p2.
intros. apply pfrage_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto.
Defined.

Lemma pfrage_nodepwp': forall d C p s p1, pfrage C p d s p1 = ⥙d⥕Ε s.
intros. apply pfrage_weakensub with empsub; auto with subdb. case_if. eapply exeqfull_refl;eauto.
Defined.

Lemma interpb_weaken': forall xd s2 xs (aeq: if NS.mem alloc (fv xd) then xs.2 = s2.2 else True), exeqFull xs s2 ((fv xd) ⨪ {·alloc·}) (⥙ xd ⥕Β xs) -> (⟦ xd ⟧Β xs) = (⟦ xd ⟧Β s2).
intros. unfold Interpb. apply interpb_weakensub with empsub; auto with subdb.
Defined.

Lemma pfragb_weaken': forall xd s2 xs (aeq: if NS.mem alloc (fv xd) then xs.2 = s2.2 else True), exeqFull xs s2 ((fv xd) ⨪ {·alloc·}) (⥙ xd ⥕Β xs) -> (⥙ xd ⥕Β xs) = (⥙ xd ⥕Β s2).
intros. unfold Pfragb. apply pfragb_weakensub with empsub; auto with subdb.
Defined.

Lemma pfrage_weaken': forall xd s2 xs (aeq: if NS.mem alloc (fve xd) then xs.2 = s2.2 else True), exeqFull xs s2 ((fve xd) ⨪ {·alloc·})(⥙ xd ⥕Ε xs) -> (⥙ xd ⥕Ε xs) = (⥙ xd ⥕Ε s2).
intros. unfold Pfrage. apply pfrage_weakensub with empsub; auto with subdb.
Defined.

Lemma interpe_weaken': forall xd s2 xs (aeq: if NS.mem alloc (fve xd) then xs.2 = s2.2 else True), exeqFull xs s2 ((fve xd) ⨪ {·alloc·}) (⥙ xd ⥕Ε xs) -> (⟦ xd ⟧Ε xs) = (⟦ xd ⟧Ε s2).
intros. unfold Interpe. apply interpe_weakensub with empsub; auto with subdb.
Defined.



Fixpoint nlist_to_ns (nl: list nat) :=
  match nl with 
  | nil => NS.empty 
  | a:: nl' => NS.add a (nlist_to_ns nl')
  end.

(*no fv -> exeq, this lemma is the same as substl_notin*)
Lemma exeqf_substl: forall sub  s A, NS.Empty (NS.inter (nlist_to_ns (split sub).1) A) -> eqxcptS (s) (substl s sub) A.
induction sub;unfold eqxcptS;intros.
-
  simpl. auto.
-
  (*n notin A*)
  destruct a.
  simpl. 
  simpl in H. destruct (split sub). simpl in H. 

  case_eq(Nat.eq_dec x n);intros.
  +
    rewrite e in H0. apply NS.mem_2 in H0. unfold NS.Empty in H. assert (NS.In n (NS.inter (NS.add n (nlist_to_ns l)) A)). NSDecide.fsetdec.
    apply H in H2. contradiction.
  +
    unfold eqxcptS in IHsub.
    eapply IHsub;eauto.
    simpl.  NSDecide.fsetdec.
Defined.
Lemma substl_notin: forall x l s, ~List.In x (split l).1 -> substl s l x = s x.
induction l;intros.
-
  simpl. auto.
-
  simpl in H. destruct a as [k v]. destruct (split l). simpl in *. 
  
  simpl. case_eq(Nat.eq_dec x k);intros. assert (k = x \/ In x l0). left;auto. apply H in H1. contradiction.
  apply IHl. intro. assert (k = x \/ In x l0). right;auto. apply H in H2. auto. 
Defined.
Lemma ninhead: forall n params, ~ In alloc (n :: params) -> n <> alloc.
intros.
intro eq. assert (In alloc (n :: params)). constructor. auto. apply H in H0. auto.
Defined.
Lemma nincons: forall n params, ~ In alloc (n :: params) -> ~ In alloc params.
intros.
intro eq. assert (In alloc (n :: params)). simpl. right. auto. apply H in H0. auto.
Defined.


(*we don't need a trunc_notin lemma, cos notin means null*)
Lemma trunc_in: forall zs s params i (nal: ~ List.In alloc params) (nal2: ~ List.In alloc zs) (nod: List.NoDup params), 
i < Datatypes.length params -> List.length zs = List.length params ->
(s[{`!map (fun xe : var * exprd => (xe.1, (⟦ xe.2 ⟧Ε) s)) (combine (params) (map evar (zs)))!`}]).1.1 (nth i (params) alloc) 
= s.1.1 (nth i (zs) alloc).
induction zs;intros.
-
  simpl. simpl in H0.
  rewrite <- H0 in H. lia.
-
  assert (a<>alloc). eapply ninhead;eauto.
  simpl in H0. destruct params. inversion H0. simpl in H0.
  
  destruct i. simpl. rewrite (eqb_refl n). ie. ne H1. auto. 
  simpl in H.
  assert (nth i params alloc =? n = false). inversion nod. simpl in H. apply lt_S_n in H.
  case_eq((nth i params alloc =? n));intros;auto. assert (In (nth i params alloc) params). apply nth_In;auto. apply Nat.eqb_eq in H6. rewrite H6 in H7. apply H4 in H7. contradiction.
  simpl nth. unfold state_trunc. simpl. rewrite H2. apply IHzs.
  eapply nincons;eauto. eapply nincons;eauto. inversion nod. auto. lia. auto. 
Defined.



(* -> eqxcptH h (updfield' h p f v)  *)


(*----------The Definition Lemmas----------*)
Lemma conj_def: forall A B s, ⟦A </\>· B⟧Β s = (⟦A⟧Β s) && (⟦B⟧Β s).
intros. ib. rewrite (interpb_nodepwp' A). rewrite (interpb_nodepwp' B). auto. 
Defined.
Lemma conj_pdef: forall A B s, ⥙A </\>· B⥕Β s = (⥙A⥕Β s) ⋓ (⥙B⥕Β s).
intros. pb. rewrite (pfragb_nodepwp' A). rewrite (pfragb_nodepwp' B). auto. 
Defined.
Lemma sc_def: forall A B s, ⟦A <*>· B⟧Β s = ((⥙A⥕Β s) !! (⥙B⥕Β s)) && (⟦A⟧Β s) && (⟦B⟧Β s).
intros. ib. rewrite (interpb_nodepwp' A). rewrite (interpb_nodepwp' B). unfold disjoint.
rewrite (pfragb_nodepwp' A). rewrite (pfragb_nodepwp' B). auto. 
Defined.
Lemma sc_pdef: forall A B s, ⥙A <*>· B⥕Β s = (⥙A⥕Β s) ⋓ (⥙B⥕Β s).
intros. pb. rewrite (pfragb_nodepwp' A). rewrite (pfragb_nodepwp' B). auto. 
Defined.

Lemma bif_def: forall test A B s, ⟦bif test then A else B⟧Β s = if ⟦test⟧β s then ⟦A⟧Β s else ⟦B⟧Β s.
intros. case_eq((⟦ test ⟧β) s);intros;ib;rewrite interpb_equation_11. 
rewrite ffffintro with (pf:=H). rewrite (interpb_nodepwp' A). auto.
rewrite ffffintrof with (pf:=H). rewrite (interpb_nodepwp' B). auto.
Defined.
Lemma bif_pdef: forall test A B s, ⥙bif test then A else B⥕Β s = if ⟦test⟧β s then ⥙A⥕Β s ⋓ (⥙ test ⥕β) s else ⥙B⥕Β s ⋓ (⥙ test ⥕β) s.
intros. case_eq((⟦ test ⟧β) s);intros;pb. 
rewrite ffffintro with (pf:=H). rewrite (pfragb_nodepwp' A). auto.
rewrite ffffintrof with (pf:=H). rewrite (pfragb_nodepwp' B). auto.
Defined.

Lemma not_def: forall A s, ⟦<!> A⟧Β s = negb (⟦A⟧Β s).
intros. ib. rewrite (interpb_nodepwp' A). auto. 
Defined.
Lemma not_pdef: forall A s, ⥙<!> A⥕Β s = (⥙A⥕Β s).
intros. pb. rewrite (pfragb_nodepwp' A). auto. 
Defined.

Lemma eq_def: forall e1 e2 s, ⟦e1 ·=· e2⟧Β s = (veq ((⟦ e1 ⟧Ε) ( s)) ((⟦ e2 ⟧Ε) ( s))).
intros. ib. auto.
Defined.
Lemma eq_pdef: forall e1 e2 s, ⥙ e1 ·=· e2 ⥕Β s = PNS.union (⥙  e1  ⥕Ε s) (⥙  e2  ⥕Ε s).
intros. pb. auto.
Defined.

Lemma pcall_def: forall e C neq p s, ⟦(e @ C ∥ neq ⟼ p ())⟧Β s = ⟦(getp (gamma C) p)⟧Β (s[{`![(this, (⟦ e ⟧Ε s))]!`}]).
intros. ib. rewrite (interpb_nodepwp' ((getp (gamma C) p))). auto.
Defined.
Lemma pcall_pdef: forall e C neq p s, ⥙(e @ C ∥ neq ⟼ p ())⥕Β s = ⥙(getp (gamma C) p)⥕Β (s[{`![(this, (⟦ e ⟧Ε s))]!`}]) ⋓ ⥙e⥕Ε s.
intros. pb. pe. rewrite (pfragb_nodepwp' ((getp (gamma C) p))). auto.
Defined.

Lemma bbop_def: forall (e1 e2 : exprd) (s : state) op, ⟦  b_ e1 op e2 ⟧Β s = (((bops op) ((⟦e1⟧Ε) ( s)) ((⟦e2⟧Ε) ( s)))) .
intros. ib. auto. 
Defined.
Lemma bbop_pdef: forall (e1 e2: exprd) (s : state) op, ⥙ b_ e1 op e2 ⥕Β s = (⥙e1⥕Ε s) ⋓ (⥙e2⥕Ε s).
intros. pb. auto.
Defined.
Lemma buop_def: forall (e1: exprd) (s : state) op, ⟦  u_ op e1 ⟧Β s = (buops op) ((⟦e1⟧Ε) ( s)).
intros. ib. auto. 
Defined.
Lemma buop_pdef: forall (e1: exprd) (s : state) op, ⥙ u_ op e1 ⥕Β s = (⥙e1⥕Ε s).
intros. pb. auto.
Defined.


Lemma acc_def: forall e s, ⟦ dbacc e ⟧Β s = true.
intros. ib. auto.
Defined.
Lemma acc_pdef: forall e s, ⥙ dbacc e ⥕Β s = (⥙  e  ⥕Ε s).
intros. pb. auto. 
Defined.


Lemma eval_def: forall (v : val) (s : state), ⟦  ! v  ⟧Ε s = v.
intros. ie. auto.
Defined.
Lemma eval_pdef: forall (v : val) (s : state), ⥙  ! v  ⥕Ε s = PNS.empty.
intros. pe. auto.
Defined.

Lemma evar_def: forall (v : var) (s : state), ⟦  ′ v  ⟧Ε s = if Nat.eq_dec v alloc then vset s.2 else (fst (fst s)) v.
intros. ie. auto.
Defined.
Lemma evar_pdef: forall (v : var) (s : state), ⥙  ′ v  ⥕Ε s = PNS.empty.
intros. pe. auto.
Defined.
Lemma efa_def: forall (e : exprd) (s : state) f, ⟦  e …  f ⟧Ε s = (snd(fst s)) (val_to_ptr (⟦e⟧Ε s), f).
intros. ie. f_equal. rewrite (interpe_nodepwp' e). auto.
Defined.
Lemma efa_pdef: forall (e : exprd) (s : state) f, ⥙  e …  f ⥕Ε s = PNS.union (PNS.singleton (val_to_ptr (⟦e⟧Ε s), f)) (⥙e⥕Ε s).
intros. pe. f_equal. rewrite (interpe_nodepwp' e). auto. rewrite (pfrage_nodepwp' e). reflexivity. 
Defined.

Lemma ebop_def: forall (e1 e2 : exprd) (s : state) op, ⟦  b' e1 op e2 ⟧Ε s = (((ebops op) ((⟦e1⟧Ε) ( s)) ((⟦e2⟧Ε) ( s)))) .
intros. ie. f_equal. apply (interpe_nodepwp' e1).   apply (interpe_nodepwp' e2). 
Defined.
Lemma ebop_pdef: forall (e1 e2: exprd) (s : state) op, ⥙ b' e1 op e2 ⥕Ε s = (⥙e1⥕Ε s) ⋓ (⥙e2⥕Ε s).
intros. pe. rewrite (pfrage_nodepwp' e1). rewrite (pfrage_nodepwp' e2). auto.
Defined.

Lemma euop_def: forall (e1 : exprd) (s : state) op, ⟦  u' op e1 ⟧Ε s = (euops op) ((⟦e1⟧Ε) ( s)) .
intros. ie. f_equal. apply (interpe_nodepwp' e1). 
Defined.
Lemma euop_pdef: forall (e1 : exprd) (s : state) op, ⥙ u' op e1 ⥕Ε s = (⥙e1⥕Ε s).
intros. pe. rewrite (pfrage_nodepwp' e1). auto.
Defined.

Global Hint Rewrite efa_pdef : esemdb.
Global Hint Rewrite efa_def : esemdb.
Global Hint Rewrite evar_pdef : esemdb.
Global Hint Rewrite evar_def : esemdb.
Global Hint Rewrite eval_pdef : esemdb.
Global Hint Rewrite eval_def : esemdb.
Global Hint Rewrite eq_def : esemdb.
Global Hint Rewrite eq_pdef : esemdb.
Global Hint Rewrite acc_pdef : esemdb.
Global Hint Rewrite acc_def : esemdb.
Global Hint Rewrite conj_def : esemdb.
Global Hint Rewrite conj_pdef : esemdb.
Global Hint Rewrite sc_def : esemdb.
Global Hint Rewrite sc_pdef : esemdb.
Global Hint Rewrite bif_def : esemdb.
Global Hint Rewrite bif_pdef : esemdb.
Global Hint Rewrite not_def : esemdb.
Global Hint Rewrite not_pdef : esemdb.
Global Hint Rewrite bbop_def : esemdb.
Global Hint Rewrite bbop_pdef : esemdb.
Global Hint Rewrite buop_def : esemdb.
Global Hint Rewrite buop_pdef : esemdb.
Global Hint Rewrite ebop_def : esemdb.
Global Hint Rewrite ebop_pdef : esemdb.
Global Hint Rewrite euop_def : esemdb.
Global Hint Rewrite euop_pdef : esemdb.
(*we prefer the natural rewriting with free lemmas*)
(* Global Hint Rewrite pcall_def : esemdb.
Global Hint Rewrite pcall_pdef : esemdb. *)


(* Lemma euops_def:  *)
(* Goal forall s, ⟦ b_ (  (′ this)  … next) `∈(  (′ this)  … repr) ⟧Β s = true.
intros. autorewrite with esemdb. autounfold with esemdb. simpl. *)
Definition exsub P e:= forall s, PS.Subset (reduce (⥙P⥕Β s)) (val_to_set (⟦e⟧Ε s)).
Lemma disj0: forall Q x, ~PS.In x.1 (reduce Q) -> ~PNS.In x Q.
apply (@PNS'.set_induction (fun Q => forall x, ~PS.In x.1 (reduce Q) -> ~ PNS.In x Q)).
admit.
intros.
apply PNS'.Add_Equal in H1. rewrite H1.
unfold reduce in H2.
apply (fold_add_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H0.
apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H1.
rewrite H1 in H2. rewrite H0 in H2.
unfold not. intros.
assert (~PS.E.eq x0.1 x.1). PSDecide.fsetdec.
assert (~PS.In x0.1 (⌊'' fun loc : PNS.elt => [eta PS.add loc.1] ''⌋ s
           ▹ PS.empty)). PSDecide.fsetdec.

apply PNS_.add_iff in H3. destruct H3.
unfold PS.E.eq in H4. rewrite H3 in H4. contradiction.
assert (~PNS.In x0 s). apply H;auto. contradiction. 
Admitted.

Lemma disj1: forall A B, PS.equal (PS.inter (reduce A) (reduce B)) PS.empty -> PNS.equal (PNS.inter A B) PNS.empty.
apply (@PNS'.set_induction (fun A0 => (forall B : PNS.t,
PS.equal (PS.inter (reduce A0) (reduce B)) PS.empty ->
PNS.equal (PNS.inter A0 B) PNS.empty))).
admit.
intros.
apply PNS'.Add_Equal in H1. rewrite H1. 
assert (PNS.Equal (PNS.inter s B) PNS.empty /\ ~ PNS.In x B). 

apply PS.equal_2 in H2. 
unfold reduce in H2. 
apply (fold_add_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H0.
apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H1. rewrite H1 in H2. rewrite H0 in H2.
assert (~PS.In x.1 (( (⌊'' fun loc : PNS.elt => [eta PS.add loc.1] ''⌋ B
           ▹ PS.empty)))). PSDecide.fsetdec.
assert (PS.Equal
       (PS.inter
          (
             (⌊'' fun loc : PNS.elt => [eta PS.add loc.1] ''⌋ s
              ▹ PS.empty))
          (⌊'' fun loc : PNS.elt => [eta PS.add loc.1] ''⌋ B
           ▹ PS.empty)) PS.empty). PSDecide.fsetdec.
constructor.
apply PNS.equal_2.
apply (H B).
apply PS.equal_1. auto.

fold reduce in H2.
apply disj0;auto.
apply PNS.equal_1. PNSDecide.fsetdec.
Admitted.

Lemma disj2: forall a b A B, PS.Subset a A -> PS.Subset b B -> PS.equal (PS.inter A B) PS.empty -> PS.equal (PS.inter a b) PS.empty.
Admitted.

Lemma orb_rfalse: forall a, a || false = a.
Proof.
    intros.
    case_eq(a);auto.
Defined.
Lemma reduce_singleton: forall x, PS.Equal (reduce (PNS.singleton x)) (PS.singleton x.1).
Proof.
    intros.
    assert (PNS.Equal (PNS.singleton x) (PNS.add x PNS.empty)). PNSDecide.fsetdec.
    unfold reduce.
    
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1] ) PS.empty) in H.
    rewrite H. 
    assert (~PNS.In x PNS.empty). PNSDecide.fsetdec.
    apply (fold_add_pns (fun loc : PNS.elt => [eta PS.add loc.1] ) PS.empty) in H0.
    rewrite H0.
    rewrite PNS'.fold_empty.
    auto.
Qed.
Lemma reduce_empty: PS.Equal (reduce (PNS.empty)) (PS.empty).
Proof.
    intros. 
    unfold reduce.
    rewrite PNS'.fold_empty.
    PSDecide.fsetdec.
Qed.
Lemma disj3: forall Q x, PNS.In x ( Q) -> PS.In x.1 (reduce Q).
  apply (@PNS'.set_induction (fun Q => forall x, PNS.In x ( Q) -> PS.In x.1 (reduce Q)));intros.
  -
  unfold PNS.Empty in H. apply H in H0. contradiction.
  -
  apply PNS'.Add_Equal in H1. 
  apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H1 as H1e.
  rewrite H1e. 
  apply (fold_add_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H0 as H0e.
  rewrite H0e.
  case_eq(PNS.E.eq_dec x0 x);intros.
  apply PS.add_1. rewrite e. auto.
  apply PS.add_2.
  apply H;auto.
  PNSDecide.fsetdec. 
Defined.
(*"but not reverse"*)
Lemma disj4: forall A B, PNS.Subset A B -> PS.Subset (reduce A) (reduce B).
Admitted.
Lemma reduce_union: forall A B, PS.Equal (reduce (PNS.union A B)) (PS.union (reduce A) (reduce B)).
Proof.
    apply (@PNS'.set_induction (fun A => (forall B : PNS.t,
    PS.Equal (reduce (PNS.union A B)) (PS.union (reduce A) (reduce B)))));intros.
    -
    assert (PNS.Equal s PNS.empty). PNSDecide.fsetdec.
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H0.
    rewrite H0. 
    assert (PNS.Equal (PNS.union s B) B). PNSDecide.fsetdec.
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H1.
    rewrite H1.
    PSDecide.fsetdec.
    -
    apply PNS'.Add_Equal in H1.
    assert (PNS.Equal (PNS.union s' B) (PNS.union (PNS.add x s) B)). PNSDecide.fsetdec.
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H2 as H2e.
    rewrite H2e.
    assert (PNS.Equal (PNS.union (PNS.add x s) B) (PNS.add x (PNS.union s B))). apply PNS'.union_add.
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H1 as H1e.
    rewrite H1e.
    
    apply (fold_add_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H0 as H0e.
    rewrite H0e.
    case_eq (PNS.mem x B);intros.
    +
    apply PNS.mem_2 in H4.

    assert (PNS.Equal (PNS.union (PNS.add x s) B ) ( (PNS.add x (PNS.union s B)))). clear H. PNSDecide.fsetdec.
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H5 as H5e.
    assert (PNS.In x (PNS.union s B)). PNSDecide.fsetdec.
    assert (PNS.Equal (PNS.add x (PNS.union s B)) (PNS.union s B)). apply PNS'.add_equal. auto. (*TODO: why so slow? clear H. clear H1. clear H2. clear H2e. clear H3. clear H0. clear H4. clear H5.  PNSDecide.fsetdec.*)
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H7 as H7e.
    rewrite H5e. rewrite H7e.
    assert (PS.In x.1 (PS.union (reduce s) (reduce B))). assert(PS.In x.1 (reduce B)). apply disj3;auto. apply PS.union_3. auto. 
    assert (PS.Equal (PS.union (PS.add x.1 (reduce s)) (reduce B)) (PS.union ((reduce s)) (reduce B))).
    PSDecide.fsetdec.
    rewrite H9.
    apply H.


    +
    apply PNS_.not_mem_iff in H4. 
    assert (~PNS.In x (PNS.union s B)). apply PNS'.not_in_union;auto. 
    apply (fold_equal_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H3 as H3e.
    rewrite H3e.
    apply (fold_add_pns (fun loc : PNS.elt => [eta PS.add loc.1]) PS.empty) in H5 as H5e.
    rewrite H5e.
    pose (H B) as HB. unfold reduce in HB. rewrite HB.

    
    
    PSDecide.fsetdec.
Defined.

Lemma pns_emp_ps: forall A, PNS.Empty A -> PS.Empty (reduce A).
Admitted.

Lemma disj5: forall A B, PS.Empty ((reduce A) ⩄ (reduce B)) -> PNS.Empty (A ⋒ B).
Admitted. 
  
Ltac pns_to_ns :=
repeat (match goal with
| [H: (PNS.Subset ?A ?B) |- _ ] =>
  apply disj4 in H
| [H: (PNS.In ?A ?B) |- _ ] =>
  apply disj3 in H
| [H: (PNS.Empty ?A) |- _ ] =>
  apply pns_emp_ps in H
end).

Global Hint Rewrite interpb_nodepwp': interpdb. 
Global Hint Rewrite pfragb_nodepwp': interpdb. 
Global Hint Rewrite reduce_union: folddb.
Global Hint Rewrite reduce_singleton: folddb.
Notation "⇑ₘ l" := (NM'.of_list l) (at level 40).
Notation "⇑ₛ l" := (NS'.of_list l) (at level 40).

(*do we allow alloc in params? of course not, but in args, can't in args neither, args also rely on stack semantics?*)
(*the stack after truncsub is good*)
(*we require alloc not in lists, and does not require allocset, analyzing the other three conditions (in both and in just one) is tedious*)
Lemma args_srs: forall zs params (s t:state) (nal: ~ List.In alloc params) (nal2: ~ List.In alloc zs)
(leq: List.length zs = List.length params)
(eqe: forall i, i < List.length params -> s.1.1 (List.nth i params alloc) = t.1.1 (List.nth i zs alloc)),
state_resp_sub s t 
(⇑ₘ combine params (map varpexpr (zs))).
intro. induction zs;intros.
-
  simpl. simpl in leq. apply esym in leq. apply length_zero_iff_nil in leq. rewrite leq. simpl.
  apply emp_srs.
-
  simpl in leq. destruct params. inversion leq. simpl in leq.
  simpl.
  (* unfold state_trunc. simpl. unfold state_trunc in IHzs. *)
  (*n:params, a: zs*)
  unfold state_resp_sub. intros. unfold NM'.uncurry in H. simpl in H. apply NM.find_2 in H.
  apply NM_.add_mapsto_iff in H. destruct H.
  --
    destruct H. rewrite <-H0. simpl. 

    pose (eqe 0) as eqe'. simpl in eqe'. subst n. 
    assert (v <> alloc). eapply ninhead;eauto. 
    assert (a <> alloc). eapply ninhead;eauto. 
    simpl. unfold readvar. simpl. ne H1. ne H. rewrite eqe'. auto. lia.
  --
    destruct H as [H H'].
    assert (~ In alloc (params)) as nal'. eapply nincons;eauto.
    assert (~ In alloc (zs)) as nal2'. eapply nincons;eauto.
    inversion leq. apply IHzs with (s:=s) (t:=t) in H1;auto. unfold state_resp_sub in H1.
    apply H1. apply NM.find_1 in H'. auto.
    intros. pose (eqe (S i)) as eqe'. simpl in eqe'. apply eqe'. lia. 
Defined.

Definition Disjoint P P' R := forall s, ⟦P⟧Β s -> (⥙P'⥕Β s) !! (⥙R⥕Β s).
Lemma nth_neq: forall x zs i, ~ In x zs -> i < Datatypes.length (zs) -> (nth i (zs) alloc) <> x.
intros. intro eq1. assert (In x zs). rewrite <- eq1. apply nth_In. auto. apply H in H1;auto.
Defined. 
Lemma ninsing: forall (x z:nat), z <> x  -> ~ In (z) [x].
intros. simpl. intro. destruct H0;try contradiction. rewrite H0 in H. contradiction.
Defined.
Lemma nth_next: forall i (x:nat) l d, (nth (S i) (x :: l) d) = nth i l d. simpl. auto. Defined.
Lemma unfolddb: forall C x neq p (ne1: x<>alloc), ((′ x) @ C ∥ neq ⟼ p ()) ⇒ ((getp (gamma C) p){`empsub[<this ↦ varpexpr x>]`}β).
Proof.
  intros. 
  intro s. apply impbb. intros.
  rewrite pcall_def in H. ib. ibin H. erewrite <- interpb_weakensub. 
  
  apply H. reflexivity.
  case_if. 
  -
    unfold exeqFull. constructor.
    unfold eqxcptS. intros.
    assert (NS.In this (dom_nm (empsub [<this ↦ varpexpr x >]))). apply nfind_indom with (varpexpr x);auto. 
    assert (((fv (getp (gamma C) p))) ⊆ {·this·}). apply predfv.
    assert (~NS.In x0 ((fv (getp (gamma C) p)  ⨪ dom_nm (empsub [<this ↦ varpexpr x >])) ⨪ ({·alloc·}))).
    NSDecide.fsetdec. handle_sets. apply H3 in H0. contradiction.
    apply exeqhrefl.
  -
    assert (⇑ₘ combine [this] (map varpexpr ([x])) = (empsub [<this ↦ varpexpr x >])). simpl. unfold NM'.uncurry. simpl. auto. rewrite <- H0.
    apply args_srs;auto. apply ninsing. unfold alloc,this;auto. apply ninsing. auto.
    intros. simpl in H1. destruct i. unfold state_trunc. simpl.
    ie. ne ne1. auto. lia. 
  (*we can drop neq1 by not using args_srs, since allocsets are equal, and the twwo indexs become the same by the nature of trunc*)
  (* unfold state_resp_sub. intros. 
  apply NM.find_2 in H0. apply NM_.add_mapsto_iff in H0. destruct H0.
  destruct H0. rewrite <- H1. simpl. rewrite <- H0. unfold state_trunc. unfold readvar.
  simpl. ie.  apply veqrefl.
  destruct H0. apply NM.empty_1 in H1. contradiction. *)
Defined.
Lemma unfoldpfrag: forall C x neq p s (ne1: x<>alloc), (⥙((′ x) @ C ∥ neq ⟼ p ())⥕Β s) ⩶ (⥙((getp (gamma C) p){`empsub[<this ↦ varpexpr x>]`}β)⥕Β s).
  intros. 
  rewrite pcall_pdef. pb. erewrite <- pfragb_weakensub with (xc1:=Object)(xp1:=mainb)(xdsub:=(getp (gamma C) p){`empsub [<this ↦ varpexpr x >] `}β) (xs:=s[{`![(this, (⟦  ′ x  ⟧Ε) s)]!`}]) (p1:= (mainfree (getp (gamma C) p)s[{`![(this, (⟦  ′ x  ⟧Ε) s)]!`}]) );auto.
  rewrite evar_pdef. PNSDecide.fsetdec.
  case_if.
  -
    unfold exeqFull. constructor.
    unfold eqxcptS. intros.
    assert (NS.In this (dom_nm (empsub [<this ↦ varpexpr x >]))). apply nfind_indom with (varpexpr x);auto. 
    assert (((fv (getp (gamma C) p))) ⊆ {·this·}). apply predfv.
    assert (~NS.In x0 ((fv (getp (gamma C) p)  ⨪ dom_nm (empsub [<this ↦ varpexpr x >])) ⨪ ({·alloc·}))).
    NSDecide.fsetdec. handle_sets. apply H2 in H. contradiction.
    apply exeqhrefl.
  -
    assert (⇑ₘ combine [this] (map varpexpr ([x])) = (empsub [<this ↦ varpexpr x >])). simpl. unfold NM'.uncurry. simpl. auto. rewrite <- H.
    apply args_srs;auto. apply ninsing. unfold alloc,this;auto. apply ninsing. auto.
    intros. simpl in H0. destruct i. unfold state_trunc. simpl.
    ie. ne ne1. auto. lia. 
Defined.
Lemma unfoldSImp: forall C x neq p (ne1: x<>alloc), ((′ x) @ C ∥ neq ⟼ p ()) ⟹ (((getp (gamma C) p){`empsub[<this ↦ varpexpr x>]`}β)).
intros. unfold Imp. intros. apply impbb. intros. apply andbb.
eapply impbb1. 
apply unfolddb;auto. apply H.
rewrite unfoldpfrag;auto. handle_sets. PNSDecide.fsetdec.
Defined.



Lemma dbiffimp: forall P Q, P ⇔ Q -> P ⇒ Q.
unfold dbIff. unfold DBImp. intros.
apply impbb. intros. rewrite <- H. auto.
Qed.   
Lemma iffimp1: forall P Q, P ⟺ Q -> P ⟹ Q.
unfold Iff. unfold Imp. intros.
pose (H s) as H'. apply impbb. intros.
unfold is_true in H'. apply (proj1 (Bool.eqb_true_iff _ _))  in H'. rewrite H0 in H'.
apply esym in H'. 
apply andb_prop' in H'. destruct H'.
apply andbb;auto. handle_sets. PNSDecide.fsetdec.
Defined.
Lemma iffimp2: forall P Q, P ⟺ Q -> Q ⟹ P.
(* unfold Iff. unfold Imp. intros.
pose (H s) as H'. apply impbb. intros.
unfold is_true in H'. apply (proj1 (Bool.eqb_true_iff _ _))  in H'. rewrite H0 in H'. 
apply andb_prop' in H'. destruct H'.
apply andbb;auto. handle_sets. PNSDecide.fsetdec. *)
Admitted.

Lemma iffiff: forall P Q, P ⟺ Q <-> (P ⟹ Q /\ Q ⟹ P).
Admitted.
Lemma simprefl: forall P, P ⟹ P.
(* unfold Imp. intros. apply andbb. apply imprefl. apply PNS.subset_1. PNSDecide.fsetdec. 
Defined. *)
Admitted.
Lemma simptrans: forall P Q H, P ⟹ Q -> Q ⟹ H -> P ⟹ H.
Admitted.
(* Lemma unfoldSImp: forall C x neq p, ((′ x) @ C ∥ neq ⟼ p ()) ⟺ ((getp (gamma C) p) {`[(this, x)]`}β).
Admitted. *)
(* intros. unfold Iff. intros. apply andbb.
assert (((⟦  e @ C ∥ neq ⟼ p () ⟧Β) s) = ((⟦ (getp (gamma C) p) {e // this }β ⟧Β) s)).
apply unfolddb. rewrite H. admit.
apply PNS.equal_1. symmetry. apply PNS.equal_2.
(* apply unfoldpfrag. *)
Admitted. *)

Lemma imprefl: forall P, P ⇒ P.
unfold DBImp. intros. apply impbb. auto.
Defined.


Lemma iffsym: forall P Q, P ⇔ Q -> Q ⇔ P.
unfold dbIff. intros.
auto.
Qed.


Lemma siffsym: forall P Q, P ⟺ Q -> Q ⟺ P.
Admitted.

Lemma ifImp1: forall P1 Q1 P2 Q2 test, P1 ⟹ Q1 -> P2 ⟹ Q2 -> (bif test then P1 else P2) ⟹ (bif test then Q1 else Q2).
Admitted.


Lemma sc_l1: forall P e, P <*>· e ⇒ e.
Proof.
  intros. intro s.
  apply impbb;intros.
  rewrite sc_def in H. destruct_andb. auto.
Defined.

Lemma sc_l: forall P e, P <*>· e ⟹ e.
  intros. intro s.
  apply impbb;intros.
  rewrite sc_def in H. destruct_andb. apply andbb. auto.
  rewrite sc_pdef. apply PNS.subset_1. PNSDecide.fsetdec.
Defined.
Require Import Btauto.
Lemma sccom: forall P Q, (P <*>· Q) ⟺ (Q <*>· P).
intros. intro s. rewrite sc_def. rewrite sc_def. rewrite sc_pdef. rewrite sc_pdef.
assert ( PNS.equal ((⥙ Q ⥕Β) s ⋓ (⥙ P ⥕Β) s) ((⥙ P ⥕Β) s ⋓ (⥙ Q ⥕Β) s)). apply PNS.equal_1. PNSDecide.fsetdec. rewrite H. simpl.
unfold pnsdisj. assert (PNS.is_empty (PNS.inter ((⥙ P ⥕Β) s) ((⥙ Q ⥕Β) s)) = PNS.is_empty (PNS.inter ((⥙ Q ⥕Β) s) ((⥙ P ⥕Β) s))).
case_eq (PNS.is_empty (PNS.inter ((⥙ P ⥕Β) s) ((⥙ Q ⥕Β) s)));intros;
case_eq (PNS.is_empty (PNS.inter ((⥙ Q ⥕Β) s) ((⥙ P ⥕Β) s)));intros;auto.
apply PNS.is_empty_2 in H0. assert (PNS.Empty (PNS.inter ((⥙ Q ⥕Β) s) ((⥙ P ⥕Β) s))). PNSDecide.fsetdec. apply PNS.is_empty_1 in H2. rewrite H2 in H1. inversion H1.
apply PNS.is_empty_2 in H1. assert (PNS.Empty (PNS.inter ((⥙ P ⥕Β) s) ((⥙ Q ⥕Β) s))). PNSDecide.fsetdec. apply PNS.is_empty_1 in H2. rewrite H2 in H0. inversion H0.
rewrite H0.
apply eqb_true_iff. btauto.
Defined.


Lemma conjcom: forall P Q, (P </\>· Q) ⟹ (Q </\>· P).
Admitted.



Ltac rewrite_esem:= autorewrite with esemdb;simpl interpbbt;simpl interpebt;simpl pfragbbt;simpl pfragebt;unfold readvar.
Ltac rewrite_esem_in H:= autorewrite with esemdb in H;simpl interpbbt in H;simpl interpebt in H;simpl pfragbbt in H;simpl pfragebt in H;unfold readvar in H.

Lemma impacc: forall P e, (forall s, ⟦P⟧Β s -> ⥙e⥕Ε s ⫅ ⥙P⥕Β s) -> P ⟹ dbacc e.
intros. 
unfold Imp. intros. apply impbb. intros. apply andbb. rewrite acc_def. auto.
rewrite_esem. handle_sets. apply H. auto. 
Defined.

Lemma scass1: forall P Q R, (P <*>· Q <*>· R) ⟹ ((P <*>· Q) <*>· R).
intros. unfold Imp. intros. apply impbb. intros.
rewrite sc_def in H. rewrite sc_def in H. repeat destruct_andb. rewrite sc_pdef in H2. apply andbb. 
-
  rewrite sc_def. rewrite sc_def.  apply andbb.
  +
    apply andbb. rewrite sc_pdef. unfold pnsdisj in *. handle_sets. PNSDecide.fsetdec.
    apply andbb;auto. apply andbb;auto.
    unfold pnsdisj in *. handle_sets.  PNSDecide.fsetdec.
  +
    auto.
-
  rewrite sc_pdef. rewrite sc_pdef. rewrite sc_pdef. rewrite sc_pdef. handle_sets. PNSDecide.fsetdec.
Defined.   
Lemma scass2: forall P Q R, ((P <*>· Q) <*>· R) ⟹ (P <*>· Q <*>· R) .
Admitted.
Lemma scass3: forall P Q R, ((P </\>· Q) <*>· R) ⟹ (P </\>· Q <*>· R) .
Admitted.
Lemma conjass1: forall P Q R, (P </\>· Q </\>· R) ⟹ ((P </\>· Q) </\>· R).
Admitted.
Lemma conjass2: forall P Q R,  ((P </\>· Q) </\>· R) ⟹ (P </\>· Q </\>· R).
Admitted.
Lemma conjass3: forall P Q R,  ((P <*>· Q) </\>· R) ⟹ (P <*>· Q </\>· R).
Admitted.


Lemma scconj: forall P Q, (P <*>· Q) ⟹ (Q </\>· P).
Admitted.
Lemma conjsc: forall P Q, pure P \/ pure Q -> (P </\>· Q) ⟹ (P <*>· Q).
Admitted.
Lemma conjintro: forall P Q1 Q2, P ⟹ Q1 -> P ⟹ Q2 -> P ⟹ (Q1 </\>· Q2).
Admitted.
Lemma conjelim1: forall P1 P2, (P1 </\>· P2) ⟹ P1.
Admitted.
Lemma conjelim2: forall P1 P2, (P1 </\>· P2) ⟹ P2.
Admitted.
Lemma conjImp1: forall P1 Q1 P2 Q2, P1 ⟹ Q1 -> P2 ⟹ Q2 -> (P1 </\>· P2) ⟹ (Q1 </\>· Q2).
(* intros. unfold Imp in *.
intros. pose (H s) as Hs. pose (H0 s) as H0s. apply andb_prop in Hs. destruct Hs. apply andb_prop in H0s. destruct H0s.
apply andbb. apply impbb. intros. unfold Interpb in H5. rewrite interpb_equation_9 in H5. apply andb_prop in H5. destruct H5.
assert ((⟦ Q1 ⟧Β) s). eapply impbb1. apply H1. unfold Interpb. erewrite <- interpb_nodepwp. apply H5.
assert ((⟦ Q2 ⟧Β) s). eapply impbb1. apply H3. unfold Interpb. erewrite <- interpb_nodepwp. apply H6.
unfold Interpb. rewrite interpb_equation_9. apply andbb.  unfold Interpb. erewrite <- interpb_nodepwp. apply H7.  unfold Interpb. erewrite <- interpb_nodepwp. apply H8.
unfold Pfragb. rewrite pfragb_equation_9. *)
Admitted.

Lemma scintro: forall P Q1 Q2, P ⟹ Q1 -> P ⟹ Q2 -> Disjoint P Q1 Q2 -> P ⟹ (Q1 <*>· Q2).
Admitted.

Lemma scImp1: forall P1 Q1 P2 Q2, P1 ⟹ Q1 -> P2 ⟹ Q2 -> (P1 <*>· P2) ⟹ (Q1 <*>· Q2).
(* intros. unfold Imp in *.
intros. pose (H s) as Hs. pose (H0 s) as H0s. apply andb_prop in Hs. destruct Hs. apply andb_prop in H0s. destruct H0s.
apply andbb. apply impbb. intros. unfold Interpb in H5. rewrite interpb_equation_10 in H5. apply andb_prop in H5. destruct H5. apply andb_prop in H6. destruct H6. 
assert ((⟦ Q1 ⟧Β) s). eapply impbb1. apply H1. unfold Interpb. erewrite <- interpb_nodepwp. apply H6.
assert ((⟦ Q2 ⟧Β) s). eapply impbb1. apply H3. unfold Interpb. erewrite <- interpb_nodepwp. apply H7. *)
Admitted.
Lemma scImp2: forall P1 P2, (P1 <*>· P2) ⟹ P1.
Admitted.
Lemma scImp3: forall P1 P2, (P1 <*>· P2) ⟹ P2.
Admitted.
Lemma conjImp2: forall P Q H, P ⇔ Q -> (H </\>· P) ⇔ (H </\>· Q).
Admitted.

Lemma conjIff1: forall P Q H, P ⇔ Q -> (P </\>· H) ⇔ (Q </\>· H).
Admitted.
Lemma conjIff2: forall P Q H, P ⇔ Q -> (H </\>· P) ⇔ (H </\>· Q).
Admitted.

(* Lemma substeqE: forall x f e s E, veq (⟦(′ x) … f⟧Ε s) (⟦ e ⟧Ε s) -> veq (⟦ dsubst1f E x f e ⟧Ε s) (⟦ E ⟧Ε s).
  induction E; auto; intros.
  -
    simpl. apply veqrefl.
  -
    destruct E.
    +
      simpl. 
      case_eq (Nat.eq_dec v x);intros. case_eq(Nat.eq_dec f0 f); intros. rewrite e1. rewrite e0.
      apply veqsym;auto.
      apply veqrefl. 
      apply veqrefl.
    +
    assert (dsubst1f (  E … f2 … f0) x f e = (dsubst1f ( E … f2) x f e) … f0). auto. rewrite H0.
    unfold Interpe. rewrite interpe_equation_2. rewrite interpe_equation_2.
    apply IHE in H. apply veqf. unfold Interpe in H. admit.
    admit.
    admit.
    admit.
    admit.
    admit.
  -
    simpl. apply veqrefl.
  -
    simpl. unfold Interpe. rewrite interpe_equation_4. rewrite interpe_equation_4.
    apply interpe_weaken. unfold exeqFulle. constructor. 
    unfold eqxcptS. intros. simpl. case_eq(x0 =? this);intros. admit. (*Ε implies ϵ*) 
    apply veqrefl.
    constructor. simpl. apply exeqhrefl. simpl. apply exeqprefl.
  admit.
  admit.
  admit.
Admitted. *)
      
(* Lemma substeq: forall x f e P s, ⟦ (′ x) … f ·=· e <*>· dbsubst1f P x f e ⟧Β s = ⟦(′ x) … f ·=· e <*>· P ⟧Β s.
Proof.
  induction P;intros;unfold Interpb in *.
  -
    case_eq(interpb Object mainb
  ((( ( ′ x ) … f) ·=· e) <*>· dbsubst1f (dbc b) x f e) s
  (mainfree ((( ( ′ x ) … f) ·=· e) <*>· dbsubst1f (dbc b) x f e) s));intros.
  +
  rewrite interpb_equation_10 in H;apply andb_prop in H;destruct H;apply andb_prop in H0;destruct H0;rewrite interpb_equation_2 in H0;simpl in H1.
  
  rewrite interpb_equation_10. simpl in H. simpl. rewrite H.
  rewrite interpb_equation_1. rewrite interpb_equation_1 in H1. rewrite H1. rewrite interpb_equation_2. rewrite H0.  auto.
  +
  rewrite interpb_equation_10 in H. 
  (* -
    
    rewrite interpb_equation_1. rewrite interpb_equation_1 in H1. auto.
  -
    rewrite interpb_equation_2. rewrite interpb_equation_2 in H1.
    assert (veq (⟦ dsubst1f e0 x f e ⟧Ε s) (⟦ e0 ⟧Ε s)). apply substeqE. auto.
    assert (veq (⟦ dsubst1f e1 x f e ⟧Ε s) (⟦ e1 ⟧Ε s)). apply substeqE. auto.
    apply veqtrans with ((⟦ dsubst1f e1 x f e ⟧Ε) s);auto. apply veqtrans with ((⟦ dsubst1f e0 x f e ⟧Ε) s);auto.  apply veqsym. auto.
  (* - *)
    (*all relations must respect veq*)
  admit.
  admit.
  admit.
  admit.
  -
    rewrite interpb_equation_7. rewrite interpb_equation_7 in H1.
    erewrite interpb_weaken. apply H1. unfold exeqFull. constructor. 
    unfold eqxcptS. intros. simpl. case_eq(x0 =? this);intros. apply veqsym. apply substeqE. auto.
    apply veqrefl.
    constructor. simpl. apply exeqhrefl. simpl. apply exeqprefl.
    auto.
  -
    rewrite interpb_equation_8. rewrite interpb_equation_8 in H1. *)

Admitted. *)

(* *)
Lemma localize: forall x f y P, (((′ y) ·=· ((′ x) … f)) </\>· P) ⟹ (((′ y) ·=· ((′ x) … f)) </\>· dbsubst1f P x f y).
  (* intros. unfold Imp.
  intros. apply andbb.
  apply impbb. intros. rewrite substeq in H. unfold Interpb in *. rewrite interpb_equation_10 in H. apply andb_prop in H. destruct H. apply andb_prop in H0. destruct H0.
  erewrite interpb_nodepwp. auto. apply H1.
  (*although subst1f may decrease by remove x.f, but it is included in the equality*)
  admit.  *)
Admitted.

(* Lemma substeq2: forall x f e P s, ⟦ e ·=· ((′ x) … f) </\>· dbsubst1f P x f e ⟧Β s = ⟦ e ·=· ((′ x) … f) </\>· P ⟧Β s.
Admitted.  *)
Lemma prepare_write: forall x f y P, (forall s, ⟦(((′ y) ·=· ((′ x) … f)) </\>· P)⟧Β s -> (⥙((′ x) … f)⥕Ε s) !! (⥙(dbsubst1f P x f y)⥕Β s)) -> 
(((′ y) ·=· ((′ x) … f)) </\>· P) ⟹ ((dbacc ((′ x) … f)) <*>· dbsubst1f P x f y). 
  (* intros. unfold Imp.
  intros. apply andbb.
  apply impbb. intros. pose H0 as H00. rewrite <- substeq2 in H00.
  unfold Interpb in *.
  apply (H s) in H0 as H0'.
  rewrite interpb_equation_9 in H0. apply andb_prop in H0. destruct H0.
  rewrite interpb_equation_10. apply andbb. 
  unfold pnsdisj. unfold Pfragb. rewrite pfragb_equation_6.
  unfold pnsdisj in H0'. unfold Pfragb in H0'.  auto.
  apply andbb. rewrite interpb_equation_6. auto. 
   
  rewrite interpb_equation_9 in H00. apply andb_prop in H00. destruct H00.
  erewrite interpb_nodepwp. auto. apply H3. *)
  (*subst1f would decrease by remove x.f*)
  admit.
Admitted.

Definition only_dependent dP (xs: NS.t) := 
forall (stk1 stk2:stack) h pm, (forall x, if NS.mem x xs then stk1 x = stk2 x else True) -> 
⟦dP⟧Β (stk1, h,pm) -> ⟦dP⟧Β (stk2, h,pm) /\ 
⥙dP⥕Β (((stk1, h,pm):state)) = ⥙dP⥕Β ((stk2, h,pm):state).

Definition syn_not_dependent(d: dbexp) (xs: NS.t):= NS.Empty (NS.inter xs (fv d)).


(*----------ClosingSub Lemmas----------*)
Definition csube (e: exprd) (s:stack): synsubst := 
 ⌊ (fun n sub => NM.add n (valpexpr (s n)) sub) ⌋ (fve e) ▹ empsub. 
Definition closing(e: exprd) (s:stack): exprd := e {`csube e s`}ϵ.
(* Definition closing: forall (e: exprd) (s:stack), exprd := fun e s => e {`csube e s`}ϵ. *)

Definition csub (e: dbexp) (s:stack): synsubst := 
 ⌊ (fun n sub => NM.add n (valpexpr (s n)) sub) ⌋ (fv e) ▹ empsub. 

(*this is weaker: maybe the expr after sub still contains fv*)
Lemma csub_fv1: forall xd s, (fv xd ⨪ dom_nm (csub xd s)) = NS.empty.
Admitted. 
(*for any state s', for any variable x, readvar xs x = xs.1.1 x, this only holds if alloc is not in xd*)
Lemma csub_srs: forall xs xd s' stk, NS.mem alloc (fv xd) = false -> eqxcptS xs.1.1 stk (fv xd) -> state_resp_sub xs s' (csub xd stk).
Admitted.
(*this is stronger*)
Lemma csub_fv2: forall xd s, fv xd {`csub xd s `}β = NS.empty.
Admitted.




Lemma closinginterpb: forall xc xp (xs:state) xd (s':state) (stk:stack) (seq: eqxcptS xs.1.1 stk (fv xd)) ee ee' , s'.1.2 = xs.1.2 -> NS.mem alloc (fv xd) = false -> 

@interpb xc xp xd xs (((ee'))) = @interpb xc xp ((xd){` csub xd stk `}β) s' (ee).
intros. eapply interpb_weakensub; auto.
case_if. assert (NS.mem alloc (fv xd)). handle_sets. NSDecide.fsetdec. rewrite H2 in H0. inversion H0.
unfold exeqFull. constructor. rewrite csub_fv1. eapply exeqfsetsub with (A:=∅). NSDecide.fsetdec. apply exeq_emp. rewrite H. apply exeqhrefl.
(* rewrite seq0. *)
apply csub_srs; auto.
Defined.
Lemma closingspfragb: forall xc xp xs xd s' stk (seq: eqxcptS xs.1.1 stk (fv xd)) ee ee', s'.1.2 = xs.1.2 -> NS.mem alloc (fv xd) = false -> 
@pfragb xc xp xd xs (((ee'))) = @pfragb xc xp ((xd){` csub xd stk `}β) s' (ee).
intros. eapply pfragb_weakensub; auto.
case_if. assert (NS.mem alloc (fv xd)). handle_sets. NSDecide.fsetdec. rewrite H2 in H0. inversion H0.
unfold exeqFull. constructor. rewrite csub_fv1. eapply exeqfsetsub with (A:=∅). NSDecide.fsetdec. apply exeq_emp. rewrite H. apply exeqhrefl.
apply csub_srs; auto.
Defined.

Obligation Tactic := idtac.
From mathcomp Require Import ssreflect.


Lemma dbsat_def: forall {dP dQ} s, 
(⟦ dP <*>· dQ ⟧𝚩) s <-> ⟦ dP ⟧Β s /\ ⟦ dQ ⟧Β s /\ ((⥙dP⥕Β s) !! (⥙dQ⥕Β s)) /\ (PNS.union (⥙dP⥕Β s) (⥙dQ⥕Β s)) ◄ s.2.
Proof.
  intros.
  split.
  intros.
  unfold dbsat in H.
  
  apply andb_prop in H. destruct H. rewrite sc_def in H. rewrite sc_pdef in H0.
  apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.

  constructor;auto.
  intros. unfold dbsat. rewrite sc_def. rewrite sc_pdef. 
  destruct H as [H1 [H2 [H3 H4]]]. auto. 
Defined.


Definition init (a:var) (C:classname):= ( ⌊ (fun f Q => dbsc (dbacc ((′ a) … f)) Q)⌋ (getf (gamma C)) ▹ dbt).
  
Inductive hoare: cmd -> dbexp -> dbexp -> Type := 
(*write after read stack, but fine as s' = | a => e s | x => s x: s' can be represented using s*)
| HAssign2: forall (e:exprd) P a, 
a <> alloc -> ~ NS.In a (fve e) -> ~ NS.In a (fv P) -> P ⟹ (dbacc (e)) -> 
hoare (assign a e) (P) (((′ a) ·=· e) </\>· P)
| HConseq: forall c P Q P' Q', Imp P P' -> hoare c P' Q' -> Imp Q' Q ->  hoare c P Q 
| HFrame: forall c P Q R, syn_not_dependent R (modifies c) -> 
            hoare c (P ) (Q)  -> hoare c (P <*>· R) (Q <*>· R)
| HWrite: forall f a e, a <> alloc -> pureexp e -> hoare (cwrite a f e) (dbacc ((′ a) … f)) ((((′ a) … f) ·=· (e)))
| HNew: forall D a oldalloc, a <> alloc -> oldalloc <> alloc -> oldalloc <> a -> hoare (calloc a D) ((′ oldalloc) ·=· (′ alloc)) 
(init a D <*>· (<!>(b_ (′ a) `∈ (′ oldalloc))) <*>· (b_ (′ oldalloc) `⊂ (′ alloc)) <*>· (b_ (′ a) `∈ (′ alloc)))
| HCall: forall q x y zs C, 
                        ~ List.In x (y::zs) ->  
                        ~ List.In alloc (x::y::zs) ->  
          
                        List.length zs = List.length (argsl C q) -> 
                        hoare (cdcall x y q zs) 
                        (*don't quite like this e2 equality cos not easy to obtain in hoare, but leave it for now*)
                        ((pre C q) {` ⇑ₘ (combine (this :: argsl C q) (map varpexpr (y:: zs)))`}β)
                        ((post C q){` ⇑ₘ (combine (ret :: this :: argsl C q) (map varpexpr (x:: y:: zs))) `}β)
| HSeq: forall c1 c2 P Q R, hoare c1 P Q -> hoare c2 Q R ->  hoare (seq c1 c2) P R 
| HCond: forall test c1 c2 P Q, pure test -> hoare (c1) ((test) <*>· P) Q -> hoare (c2) ((dbnot test) <*>· P) Q -> hoare (cond test c1 c2) P Q 
.
(*Q 一般来说都是atom rule的postcondition，但这个其实是连不上的
这里第一步无论如何都应该处理最初的那个chunk，所以我们step的时候考虑的也应该是那个，Q虽然不知道，但是R是知道的*)
(*post一般来说都是atom的post先回到chunk里再回到大的formula里，我觉得这里post都留做日后，还是从pre入手*)
(*1. 提供chunk和R1，证明一个simp（类似于charge的frame，可以自动做），然后去证明{chunk}c{?Q}, 最终的post为?Q<*>R1*)
(*2. chunk里获得frame，提供R2，证明chunk=>frame <*> R2（需要一些手动和lemmas），然后post1为post <*> R2*)
(*在这个过程中不去证明任意post上的imp，因为这是slp*)
(* Lemma post1: forall P P' R c Q, syn_not_dependent R (modifies c) -> hoare c P' Q -> Imp P (P' <*>· R) -> hoare P (Q <*>· R).  *)
Lemma HConl: forall c P Q P', Imp P P' -> hoare c P' Q -> hoare c P Q.
Admitted.
Lemma HConr: forall c P Q Q', Imp Q' Q -> hoare c P Q' -> hoare c P Q.
Admitted.
Lemma HAsspure: forall (e:exprd) P a, ~ NS.In a (fve e) -> ~ NS.In a (fv P) -> pureexp e -> 
hoare (assign a e) (P) ( ((′ a) ·=· e) <*>· P).
Admitted.
(* Lemma HRead2: forall f a y P, a <> y -> P ⟹ (dbacc ((′ a) … f)) -> 
(forall s, ⟦(((′ y) ·=· ((′ a) … f)) </\>· P)⟧Β s -> (⥙((′ a) … f)⥕Ε s) !! (⥙(dbsubst1f P a f (′ y))⥕Β s)) -> 
hoare (cread a f y) (P) ((((′ a) … f) ·=· (′ y)) <*>· dbsubst1f P a f (′ y) ).
Admitted.
Lemma HRead3: forall f a y P, a <> y -> P ⟹ (dbacc ((′ a) … f)) -> 
hoare (cread a f y) (P) (dbsubst1f P a f (′ y)).
Admitted. *)


(* Lemma HConseq2:  *)
(* Inductive hoaret (D:classname) (m:methodname) (sig:state): cmd -> dbexp -> dbexp -> Type := 
(*write after read stack, but fine as sig' = | a => e sig | x => sig x: sig' can be represented using sig*)
| HTAssign: forall (e:exprd) Q a, 
(* Imp (⟦(dbsubst1 Q a e)⟧Β) (readableE e) ->  *)
hoaret D m sig (assign a e) ( (Q{ e // a }β)) (Q)
| HTWrite: forall f a e, pureexp e -> hoaret D m sig (cwrite a f e) (dbacc ((′ a) … f)) ((dbeq ((′ a) … f) (e)))
| HTNew: forall C a, hoaret D m sig (calloc a C) (dbt) (init a C)
(* ((⟦ Q ⟧β) [·{` ⟦ e ⟧ϵ // a `}·]) *)
(* | HSKip: forall P, hoaret D m sig skip P P *)
(*--------------those that potentially involve "WF-carrying EAs", i.e., non-atom cases--------------*)
| HTConseq: forall c P Q P' Q', hoaret D m sig c P' Q' -> Imp P P' -> Imp Q' Q -> hoaret D m sig c P Q 
| HTCond: forall test c1 c2 P Q, pure test -> hoaret D m sig (c1) (P </\>· (test)) Q -> hoaret D m sig (c2) (P </\>· (dbnot test)) Q -> hoaret D m sig (cond test c1 c2) P Q 
| HTSeq: forall c1 c2 P Q R, hoaret D m sig c1 P Q -> hoaret D m sig c2 Q R -> hoaret D m sig (seq c1 c2) P R 
| HTFrame: forall c P Q R, syn_not_dependent R (modifies c) -> 
            hoaret D m sig c (P ) (Q)  -> hoaret D m sig c (P <*>· R) (Q <*>· R)
        
| HTCall: forall q x y zs C, 
                        x <> y /\ ~ List.In x zs ->  
                        List.length zs = List.length (argsl C q) -> 
                        hoaret D m sig (cdcall x y q zs) 
                        (*don't quite like this e2 equality cos not easy to obtain in hoare, but leave it for now*)
                        (((pre C q) {` combine (this :: argsl C q) (map evar (y:: zs))`}β) </\>· dbdecm D m sig C q y zs)
                        ((post C q){` combine (ret :: this :: argsl C q) (map evar (x:: y:: zs)) `}β)
.
Global Notation "⊢ { P }ₕ c { Q }ₕ" := (hoare c P Q) (at level 40). 
Global Notation "⊢ ⊑ ⧐λ{ P }ₕ c { Q }ₕ" := (hoare c P Q) (at level 40). 
Fixpoint sizeh{D:classname}{m:methodname} {sig: state} {c:cmd} {P Q: dbexp} (good: hoaret D m sig c P Q): nat := 
  match good with 
  | (HTAssign _ _ _ ) => 1
  | (HTCond _ _ _ _ _ _ g1 g2) => (sizeh g1) + (sizeh g2) + 1
  | (HTSeq _ _ _ _ _ g1 g2) => (sizeh g1) + (sizeh g2) + 1
  | (HTCall _ _ _ _ _ _ _) => 1 
  | (HTConseq _ _ _ _ _ g _ _) => (sizeh g) + 1
  | (HTFrame _ _ _ _ _ g) => (sizeh g) + 1
  | (HTNew _ _ ) => 1
  | (HTWrite _ _ _ _) => 1
  end.

Definition hslt {D1 D2 m1 m2 sig1 sig2 c1 c2 P1 P2 Q1 Q2} (e1: hoaret D1 m1 sig1 c1 P1 Q1) (e2: hoaret D2 m2 sig2 c2 P2 Q2) := lt (sizeh e1) (sizeh e2).
Transparent well_founded_ltof.
Transparent wf_lexprod.
Definition orderm := lexprod (classname * methodname * state) nat call_orderm lt.
(* ❷  Proof of well‑foundedness ------------------------------------- *)
Lemma orderm_wf : WellFounded orderm.
Proof. apply wf_lexprod. apply wfmm. apply lt_wf.   Defined.
#[global] Hint Resolve orderm_wf : wf.
#[global] Instance orderm_WellFounded : WellFounded orderm
  := orderm_wf. *)
End BTSemsHoare.

Module Type PWF1 (L: Measures) (L0: PWF L) (L1: PWF0 L L0).
(* Module New := ExprSems L L0. *)
Module BTH := BTSemsHoare L L0 L1.
Import L1.MM.
Import L1.MM.M.
Import BTH.
Import L.
Import L0.
(* Parameter predok: forall C p, exsub (getp (gamma C) p) ((specs C).1 p). *)
Parameter pok: forall C p, hoare (getm (gamma C) p) (pre C p) (post C p).
(* Parameter pokt: forall C p sig, hoaret C p sig (getm (gamma C) p) (pre C p) (post C p). *)
Parameter fvpre: forall C q, (fv (pre C q)) ⊆ (NS'.of_list (this :: argsl C q) ⊍ ({·alloc·})). 
Parameter fvargsl: forall C q, ~ (this = alloc \/ In alloc (argsl C q)). 
Parameter nodupargsl: forall C q, NoDup (this :: argsl C q).
Parameter fvpost: forall C q, (fv (post C q)) ⊆ (NS'.of_list (ret :: this :: argsl C q) ⊍ ({·alloc·})). 
Parameter params_not_modified: forall C q, NS.Empty (NS.inter (⇑ₛ (this::argsl C q)) (modifies (getm (gamma C) q))).
End PWF1.


Module CMDSems (L: Measures) (L0: PWF L) (L1: PWF0 L L0) (L2: PWF1 L L0 L1).

(*cann't redef New here, will cause pok mismatch*)
(*the principle seems to be "no multiple definition for the same module" *)
Import L.
Import L0.
Import L1.
Import L2.
Import L0.M.
Import L1.MM.
Import L2.BTH. 


Definition eqexcept(vs: NS.t) (s s1: stack):= (forall x, ~ NS.In x vs -> s x = s1 x).
Global Hint Rewrite reduce_union : folddb.
Global Hint Rewrite reduce_empty : folddb.

(* Ltac handle_reduce
Ltac simpl_fold *)
Lemma imp_elim: forall s P Q, P ⟹ Q -> (⟦ P ⟧Β) s -> ((⟦ Q ⟧Β) s && PNS.subset ((⥙ Q ⥕Β) s) ((⥙ P ⥕Β) s)).
intros.
  eapply impbb1;eauto.
  apply H.
Qed.
Lemma conseq_ (P Q: dbexp) (imp: Imp P Q) s (sprop:(⟦ P ⟧𝚩) s): ⟦(Q)⟧𝚩 s.
  unfold dbsat in *.
  apply andb_prop in sprop. destruct sprop.
  eapply imp_elim in imp;eauto.
  apply andb_prop in imp;auto. destruct imp.
  apply andbb. auto.
  unfold pfrag in *. 
  handle_sets. pns_to_ns. PSDecide.fsetdec.
Defined.
Program Definition conseq (P Q R: dbexp) (imp: Imp P Q) (s:{v:state| ⟦(P <*>· R)⟧𝚩 v}): {v:state| ⟦(Q <*>· R)⟧𝚩 v} := exist _ s _.
Next Obligation.
  intros. destruct s as [s sprop].
  simpl in *.
  apply dbsat_def. apply dbsat_def in sprop. 
  destruct sprop as [pok [rok [dis sub]]].
  eapply imp_elim in imp as H;eauto.
  apply andb_prop in H. destruct H.
  constructor;auto.
  constructor;auto.

  constructor. 
  unfold pnsdisj in *. handle_sets.
  PNSDecide.fsetdec. 

  unfold pfrag in *. autorewrite with folddb in *.  
  handle_sets. pns_to_ns. PSDecide.fsetdec.
Defined.


Program Definition conseq' (c:cmd) (P Q R: dbexp) (imp: Imp P Q) (s': stack) (s:{v:state| ⟦(P <*>· R)⟧𝚩 v /\ eqexcept (modifies c) (γ` v) s'})
: {v:state| ⟦(Q <*>· R)⟧𝚩 v /\ eqexcept (modifies c) (γ` v) s'} := exist _ s _.
Next Obligation.
Admitted.
Lemma eq_veq: forall a b, a = b -> veq a b. intros;subst a. apply veqrefl. Defined.
Ltac solve_stack := unfold exeqFull; constructor; [apply exeqf_substl; simpl; NSDecide.fsetdec | apply exeqhrefl].
Program Definition f'' {P R a e} (nin1: ~ NS.In a (fve e)) (nin2: ~ NS.In a (fv P)) (neq: a <> alloc) (acc: P ⟹ dbacc e) 
(dep: syn_not_dependent R (NS.singleton a))(s : {v : state | (⟦ P <*>· R ⟧𝚩) v}): 
{ v:state | (⟦ (((′ a) ·=· e) </\>· P ) <*>· R ⟧𝚩) v /\ eqexcept (NS.singleton a) (γ` v) (Γ` s)} 
:= exist _ (s[{`` [(a, ⟦ e ⟧Ε s)] ``}]) _.
Next Obligation.
  intros. simpl. destruct s as [s sprop]. simpl.
  constructor.
  -
    apply dbsat_def in sprop. apply dbsat_def.
    destruct sprop as [ sprop sprop']. destruct sprop' as [sprop' sprop'']. destruct sprop'' as [sprop'' sprop'''].
    eapply imp_elim in acc;eauto. apply andb_prop in acc. destruct acc as [acc1 acc2].
    unfold syn_not_dependent in dep. 
    constructor.
    +
      rewrite conj_def. apply andbb. rewrite eq_def. rewrite evar_def. destruct (neq_eq_def neq) as [RR HH]. rewrite HH. simpl. case_eq(Nat.eq_dec a a);intros;try contradiction.
      apply eq_veq. apply interpe_weakensub with empsub; auto with subdb. case_if. 
      solve_stack.
      erewrite interpb_weaken';eauto. case_if. 
      apply exeqfull_sym. solve_stack.
    +
    constructor.
    ++
      erewrite interpb_weaken';eauto. case_if. 
      apply exeqfull_sym. solve_stack.
    ++
    constructor.
    +++
      unfold pnsdisj in *. handle_sets. rewrite conj_pdef.
      rewrite eq_pdef. rewrite evar_pdef. rewrite acc_pdef in acc2. 
      erewrite (pfrage_weaken' e s). erewrite (pfragb_weaken' P s). erewrite (pfragb_weaken' R s).
      PNSDecide.fsetdec.
      case_if;reflexivity.
      apply exeqfull_sym. solve_stack. 
      case_if;reflexivity.
      apply exeqfull_sym. solve_stack.
      case_if;reflexivity.
      apply exeqfull_sym. solve_stack.
    +++
      unfold pfrag in *. handle_sets. rewrite conj_pdef.
      rewrite eq_pdef. rewrite evar_pdef. rewrite acc_pdef in acc2.
      autorewrite with folddb in *.  
      erewrite (pfrage_weaken' e s). erewrite (pfragb_weaken' P s). erewrite (pfragb_weaken' R s).
      simpl. pns_to_ns. PSDecide.fsetdec.
      case_if;reflexivity.
      apply exeqfull_sym. solve_stack.
      case_if;reflexivity.
      apply exeqfull_sym. solve_stack.
      case_if;reflexivity.
      apply exeqfull_sym. solve_stack.
  -
    unfold eqexcept. intros. unfold getstack. unfold getstack'. simpl. case_eq( Nat.eq_dec x a);intros.
    rewrite e0 in H. assert ( NS.In a (NS.singleton a)). NSDecide.fsetdec. apply H in H1;contradiction.
    auto.
Defined.

Definition merge_dep_assn {R1 R2: dbexp} {l: NS.t} (n1: syn_not_dependent R1 l) (n2: syn_not_dependent R2 l): syn_not_dependent (R1 <*>· R2) l.
Admitted.
(* Proof.
  unfold not_dependent. intros. simpl.
  apply sc_upME. 
  apply n1. auto.
  apply n2. auto.
Qed. *)


Program Definition sc_assoc1 {Q R' R}(s:{v:state|(⟦ (R' <*>· R) <*>· Q ⟧𝚩) v}): {v:state|(⟦ R' <*>· (R <*>· Q) ⟧𝚩) v} := s.
Next Obligation.
  intros. 
  destruct s as [s sprop]. simpl. eapply conseq_;eauto. apply scass2.
Defined.

Variable sc_assoc: forall {Q R' R}(s:{v:state|(⟦ dbsc Q (dbsc R' R)  ⟧𝚩) v}), {v:state|(⟦ dbsc (dbsc Q R') R ⟧𝚩) v}.
Lemma trans' (c:cmd) (Q R' R: dbexp) (s': stack) (s: {v : state | (⟦ Q <*>· (R' <*>· R) ⟧𝚩) v /\ eqexcept (modifies c) (γ` v) (s')}):
({v : state | (⟦ (Q <*>· R') <*>· R ⟧𝚩) v /\ eqexcept (modifies c) (γ` v) (s')}).
Admitted. 


Program Definition write' {a f R e} (neq: a <> alloc) (ispure: pureexp e)(s : {v : state | (⟦ dbsc (dbacc (( ′ a ) … f)) R ⟧𝚩) v}): { v | (⟦ dbsc ((dbeq (  (′ a)  … f) (e))) R ⟧𝚩) v /\ eqexcept (NS.empty) (γ` v) (Γ` s)} := s [`` a · f ↦ (⟦( e)⟧Ε) s ``].
Next Obligation.
  intros. simpl.
  destruct s as [s sprop]. simpl.
  constructor. unfold pureexp in ispure. 
  -  
  apply dbsat_def in sprop. 
  apply dbsat_def.
  destruct sprop as [sprop sprop']. destruct sprop' as [sprop' sprop'']. destruct sprop'' as [sprop'' sprop'''].
  autorewrite with esemdb in sprop''.  nein neq sprop''. 
  unfold pnsdisj in *.
  unfold pfrag in *.  autorewrite with esemdb in sprop'''. nein neq sprop'''. autorewrite with folddb in sprop'''.   
  assert ((⥙ R ⥕Β) s = (⥙ R ⥕Β) (s [``a · f ↦ (⟦ e ⟧Ε) s``])).
  erewrite pfragb_weaken';auto.   (*cann't reverse*)
  case_if;reflexivity.
  unfold exeqFull. constructor.
  simpl. apply exeqrefl. simpl. apply exeqh_updf.  apply sprop''.

  constructor.
  --
    autorewrite with esemdb. simpl. unfold updfield'. ne neq. 
    unfold updfield. simpl fst. unfold getstack. 
    case_eq(PNS_.eq_dec (↓ₚ s.1.1 a, f) (↓ₚ s.1.1 a, f));intros. 
    Focus 2.  unfold ptrnat_DT.eq in n. contradiction. 
    apply eq_veq. apply interpe_weaken'. case_if;reflexivity. unfold exeqFull. constructor.
    simpl. apply exeqrefl. simpl. apply exeqhempty. pe. rewrite ispure. apply PNS.empty_1. 
  --
  constructor.
  ---
    erewrite interpb_weaken';eauto.
    case_if;reflexivity.
    apply exeqfull_sym. 
    unfold exeqFull. constructor.
    simpl. apply exeqrefl. simpl.
    apply exeqh_updf. rewrite <- H. auto.
  ---
  constructor.
  ----
    autorewrite with esemdb. ne neq. simpl. unfold getstack.
    
    handle_sets. 
    (*pose (ispure (s [``a · f ↦ (⟦ e ⟧Ε) s``])) as ip. "this does not let us use the decision procedure due to the term equality"*) 
    
    rewrite <- H. 
    assert (PNS.Empty ((⥙ e ⥕Ε) (s [``a · f ↦ (⟦ e ⟧Ε) s``]))). pe. rewrite ispure. apply PNS.empty_1. 
    PNSDecide.fsetdec.
  ----
    autorewrite with esemdb. ne neq. simpl. unfold getstack.
    autorewrite with folddb. 
    assert (PNS.Empty ((⥙ e ⥕Ε) (s [``a · f ↦ (⟦ e ⟧Ε) s``]))). pe. rewrite ispure. apply PNS.empty_1. 
    pns_to_ns. 
    handle_sets.
    rewrite <- H. 
    PSDecide.fsetdec.
  -
    unfold eqexcept. intros.
    unfold getstack'. unfold getstack. simpl.  unfold getstack. auto.
Defined.

Definition comp_addr (k: (ptr)) (n: nat): nat := 
  if Nat.ltb n ((fst k)) then ((fst k)) else n.

Definition new_addr (H:PS.t):= (PS.fold comp_addr H 0) + 1.
Lemma fold_equal_A: forall {A} (f:ptr -> A -> A) i s s', PS.Equal s s' -> (⌊' f '⌋ s ▹ i) = (⌊' f '⌋ s' ▹ i).
Proof.
  intros. apply PS'.fold_equal;auto.
  unfold compat_op. auto. admit.
  unfold transpose. intros.
Admitted.
Lemma fold_add_A: forall {A} (f:ptr -> A -> A) i s x, ~PS.In x s -> (⌊' f '⌋ (PS.add x s) ▹ i) = (f x (⌊' f '⌋ s ▹ i)).
Proof.
  intros. apply PS'.fold_add;auto.
Admitted.
Lemma fold_ns_equal_A: forall {A} (f:nat -> A -> A) i s s', NS.Equal s s' -> (⌊ f ⌋ s ▹ i) = (⌊ f ⌋ s' ▹ i).
Proof.
Admitted.
Lemma fold_ns_add_A: forall {A} (f:nat -> A -> A) i s x, ~NS.In x s -> (⌊ f ⌋ (s ⨥ x) ▹ i) = (f x (⌊ f ⌋ s ▹ i)).
Proof.
  intros. 
Admitted.

Lemma mono1: forall s s' (a:ptr), ~ PS.In a s -> s' ⩵ (s ⧺ a) -> new_addr s <= new_addr s'.
intros. unfold new_addr. erewrite fold_equal_A with (s:=s'). Focus 2. apply H0.
rewrite fold_add_A;auto.  
generalize (⌊' comp_addr '⌋ s ▹ 0). intros.
unfold comp_addr. case_eq (n <? a.1 );intros. apply Nat.ltb_lt in H1. lia. auto.
Defined. 
Lemma mono3: forall s n m , n <= m -> (⌊' (fun p b=> b && (p.1 <? n)) '⌋ s ▹ true) ->  (⌊' (fun p b=> b && (p.1 <? m)) '⌋ s ▹ true).
apply (@PS'.set_induction (fun s => forall (n m0 : nat),
n <= m0 -> ⌊' fun p : PS.elt => andb^~ (p.1 <? n) '⌋ s ▹ true -> ⌊' fun p : PS.elt => andb^~ (p.1 <? m0) '⌋ s ▹ true));intros.
-
  apply PS'.empty_is_empty_1 in H.
  erewrite fold_equal_A;eauto. rewrite PS'.fold_empty. auto.
-
  apply PS'.Add_Equal in H1.
  erewrite fold_equal_A;eauto. rewrite fold_add_A;auto.
  erewrite fold_equal_A in H3;eauto. rewrite fold_add_A in H3;auto.
  apply andb_prop' in H3. destruct H3.
  rewrite (H n m0);auto.
  assert (x.1 <? m0). apply Nat.ltb_lt. apply Nat.ltb_lt in H4. lia. rewrite H5.
  auto.
Defined.
Lemma mono2: forall x n, (x.1 <? comp_addr x n + 1).
Proof.
  intros. unfold comp_addr. case_eq(n <? x.1 );intros. apply Nat.ltb_lt. lia.
  assert (~ n < x.1). intro lt1. apply Nat.ltb_lt in lt1. rewrite H in lt1. inversion lt1. apply Nat.ltb_lt. lia.
Defined.
Lemma new_addr_fresh': forall s, (⌊' (fun p b=> b && (p.1 <? new_addr s)) '⌋ s ▹ true).
apply (@PS'.set_induction (fun s => (⌊' (fun p b=> b && (p.1 <? new_addr s)) '⌋ s ▹ true)));intros.
-
  apply PS'.empty_is_empty_1 in H.
  erewrite fold_equal_A;eauto. rewrite PS'.fold_empty. auto.
-
  apply PS'.Add_Equal in H1.
  erewrite fold_equal_A;eauto.
  rewrite fold_add_A;auto.
  erewrite mono3. Focus 3. apply H.
  unfold new_addr. erewrite fold_equal_A;eauto. rewrite fold_add_A;auto. rewrite mono2. auto.
  eapply mono1;eauto.
Defined.

Lemma new_addr_fresh'': forall s (D:classname) n, (⌊' (fun p b=> b && (p.1 <? n)) '⌋ s ▹ true) -> ~ PS.In (n, D) s.
apply (@PS'.set_induction (fun s => forall (D : classname) (n:nat), (⌊' (fun p b=> b && (p.1 <? n)) '⌋ s ▹ true) -> ~ PS.In (n, D) s));intros.
-
  apply PS'.empty_is_empty_1 in H.
  PSDecide.fsetdec.
-
  apply PS'.Add_Equal in H1. rewrite H1.
  erewrite fold_equal_A in H2;eauto.
  rewrite fold_add_A in H2;auto. apply andb_prop' in H2. destruct H2.
  apply (H D) in H2;auto.
  assert (~ PS.E.eq (n, D) x). unfold not. intros. destruct x. simpl in H3. inversion H4. rewrite H6 in H3. apply Nat.ltb_lt in H3. lia. 
  PSDecide.fsetdec.
Qed.

Lemma new_addr_fresh: forall s D, ~ PS.In (new_addr s, D) s.
intros. apply new_addr_fresh''. apply new_addr_fresh'. 
Defined.
(* oldalloc <> alloc -> oldalloc <> a -> hoare (calloc a D) ((′ oldalloc) ·=· (′ alloc)) 
(init a D <*>· (<!>(b_ (′ a) `∈ (′ oldalloc))) <*>· (b_ (′ oldalloc) `⊂ (′ alloc)) <*>· (b_ (′ a) `∈ (′ alloc))) *)

Lemma neg_1: forall (A: bool), (A -> False) -> ~~ A.
intros.
case_eq(A);intros;auto.
Qed.
Lemma dbc_pdef: forall c s, (⥙ dbc c ⥕Β) s = ⦱.
Admitted.
(*直接证明disjoint*)
Lemma init_pfrag: forall a D s addr (neq: a <> alloc), (reduce ((⥙ init a D ⥕Β) ((s[{``[(a, vptr (addr, D))]``}]).1, s.2 ⧺ (addr, D)))) ⫉ {{ (addr, D)}}.
intros. unfold init. generalize (getf (gamma D)).
apply (@NS'.set_induction (fun t => reduce ((⥙ ⌊ fun f : NS.elt => [eta dbsc (dbacc ( ( ′ a ) … f))] ⌋ t ▹ ⊤⥕Β) 
((s[{``[(a, vptr (addr, D))]``}]).1, s.2 ⧺ (addr, D))) ⫉ {{(addr, D)}}));intros.
-
  apply NS'.empty_is_empty_1 in H.
  erewrite fold_ns_equal_A;eauto. rewrite NS'.fold_empty. unfold dbt.
  rewrite dbc_pdef. unfold reduce. rewrite PNS'.fold_empty. PSDecide.fsetdec.
-
  apply NS'.Add_Equal in H1.
  erewrite fold_ns_equal_A. Focus 2. apply H1.
  erewrite fold_ns_add_A;auto. autorewrite with esemdb.
  ne neq. simpl. id a. simpl. 
  autorewrite with folddb. simpl.
  PSDecide.fsetdec.    
Defined.
Program Definition new' (D: classname) (a oldalloc: var) (R: dbexp) (dep: syn_not_dependent R ({· a ·} ⨥ alloc))
(neq: a <> alloc) (neq1: oldalloc <> alloc) (neq2: oldalloc <> a) (s: {v:state | (⟦ ((′ oldalloc) ·=· (′ alloc))  <*>· R ⟧𝚩) v}): 
{v:state | (⟦(init a D <*>· (<!>(b_ (′ a) `∈ (′ oldalloc))) <*>· (b_ (′ oldalloc) `⊂ (′ alloc)) <*>· (b_ (′ a) `∈ (′ alloc))) <*>· R ⟧𝚩) v /\ eqexcept (({· a ·} ⨥ alloc)) (γ` v) (Γ` s)} := 
let addr := new_addr s.2 in let newallloc := (s.2 ⧺ ((addr, D):ptr)) in ((s[{`` [(a, ((vptr (addr, D))))] ``}]).1, newallloc).
Next Obligation.
  intros. destruct s as [s sprop]. simpl sval in *.
  constructor.
  -
    apply dbsat_def in sprop. apply dbsat_def.
    destruct sprop as [sprop sprop']. destruct sprop' as [sprop' sprop'']. destruct sprop'' as [sprop'' sprop'''].
    autorewrite with esemdb in sprop. nein neq1 sprop. idin alloc sprop. apply veqseq in sprop. 
    unfold syn_not_dependent in dep.
    autorewrite with esemdb in sprop'''. unfold pfrag in sprop'''. autorewrite with folddb in sprop'''.

    assert (((⥙ R ⥕Β) ((s[{``[(a, vptr (addr, D))]``}]).1, newallloc)) = (⥙ R ⥕Β) s) as RR.
    erewrite (pfragb_weaken' R s);auto.
    case_if. simpl. handle_sets. assert (~NS.In alloc (fv R)). NSDecide.fsetdec. apply H0 in H; contradiction.
    apply exeqfull_sym. solve_stack.
    constructor.
    --
    autorewrite with esemdb. apply andbb. apply andbb.
    unfold pnsdisj. handle_sets. PNSDecide.fsetdec.
    unfold init. admit.
    apply andbb. apply andbb. unfold pnsdisj. handle_sets. PNSDecide.fsetdec.
    autounfold with dbops. simpl. case_eq ( Nat.eq_dec a a);intros;try contradiction. case_eq (Nat.eq_dec oldalloc a);intros.
    clear H0. apply neq2 in e0. contradiction.
    ne neq.
    apply notb_prop''. apply PS_.not_mem_iff.
    handle_sets. ne neq1. rewrite sprop. unfold addr. simpl. apply new_addr_fresh.
    apply andbb. apply andbb. unfold pnsdisj. handle_sets. PNSDecide.fsetdec.
    simpl. ne neq1. ne neq2. unfold bops. simpl. unfold newallloc. unfold liftsubset.
    unfold compssubset. apply andbb. 
    handle_sets. rewrite sprop. simpl. PSDecide.fsetdec.
    assert (~ PS.Equal (↓ₛ s.1.1 oldalloc) (↓ₛ (s.2 ⧺ (addr, D)))). handle_sets.  rewrite sprop.  simpl. assert (~PS.In (addr, D) s.2). apply new_addr_fresh. PSDecide.fsetdec.
    apply neg_1;intros. handle_sets. apply H in H0. contradiction.

    unfold bops. simpl. ne neq. id a. unfold liftin. unfold add. unfold newallloc. simpl. apply PS.mem_1. PSDecide.fsetdec.
    --
    constructor.
    ---
    erewrite interpb_weaken';eauto. case_if. simpl. handle_sets. assert (~NS.In alloc (fv R)). NSDecide.fsetdec. apply H0 in H. contradiction. 
    apply exeqfull_sym.
    solve_stack.
    ---
    constructor.
    ----
    unfold pnsdisj. autorewrite with esemdb.
    rewrite RR. unfold newallloc.
    handle_sets. apply disj5. autorewrite with folddb. rewrite init_pfrag;auto.  unfold addr.
    assert (~ PS.In (new_addr s.2, D) s.2). apply new_addr_fresh. PSDecide.fsetdec.
    ----
    unfold pfrag. rewrite RR. 
    autorewrite with esemdb. autorewrite with folddb. unfold newallloc. 
    handle_sets.
    rewrite init_pfrag;auto. simpl. 
    PSDecide.fsetdec.
  -
    unfold eqexcept. intros. unfold getstack. unfold getstack'. simpl. case_eq( Nat.eq_dec x a);intros.
    rewrite e in H. assert ( NS.In a ((({·a·}) ⨥ alloc))). NSDecide.fsetdec. apply H in H1;contradiction.
    auto.
Admitted.
(* Lemma srs_weaken: forall s m' zs params a v, NM.find v m' = None ->  
        (⌈ sresp (fun x' => 
          (substl_trunc (map (fun xe => (xe.1, (⟦ xe.2 ⟧Ε) s)) (combine params (map evar zs))) x'),
            s.1.2, s.2) s ⌉ m' ▹ true) -> 
        (⌈ sresp (fun x' : var => if x' =? v then (⟦  ′ a  ⟧Ε) s else
         substl_trunc (map (fun xe => (xe.1, (⟦ xe.2 ⟧Ε) s)) (combine params (map evar zs))) x',
        s.1.2, s.2) s ⌉ m' ▹ true).
Admitted. *)



(*should be possible to merge this two lemmas, but leave it for now*)
(*the stack after fallbacking and ret subst is good*)
(* Lemma ret_srs: forall zs (s t:state) params x  
(eqe: forall i, i < List.length params -> t.1.1 (List.nth i params alloc) = s.1.1 (List.nth i zs alloc)) 
(nal: ~ List.In alloc params) (na: ret <> alloc) (na2: x<>alloc) (nal2: ~List.In alloc zs) (nal3: ~List.In x zs), List.length zs = List.length params -> 
 state_resp_sub t (substl s.1.1 [(x, (t.1.1 ret))], t.1.2, t.2)
  (⇑ₘ combine (ret :: params) (map varpexpr (x :: zs))).
intro. induction zs;intros.
-
  simpl. simpl in H. apply esym in H. apply length_zero_iff_nil in H. rewrite H. simpl.
  unfold NM'.uncurry;simpl. unfold state_resp_sub. intros.
  apply NM.find_2 in H0. apply NM_.add_mapsto_iff in H0. destruct H0.
  --
    destruct H0. rewrite <- H0. rewrite <- H1. simpl.
    unfold readvar. ne na. ne na2. simpl. id x. apply veqrefl.
  --
    destruct H0. apply NM.empty_1 in H1;auto.
-
  simpl in H. destruct params. inversion H. simpl in H.
  simpl. inversion H.
  (*v:params, a: zs*)
  unfold state_resp_sub. intros. unfold NM'.uncurry in H0. simpl in H0. apply NM.find_2 in H0.
  apply NM_.add_mapsto_iff in H0. destruct H0.
  --
    destruct H0. rewrite <- H0. rewrite <- H2. simpl.
    unfold readvar. ne na. ne na2. simpl. id x. apply veqrefl.
  --
  destruct H0. apply NM_.add_mapsto_iff in H2. destruct H2.
  ---
    destruct H2. 
    assert (n <> alloc). intro eq. assert (In alloc (n :: params)). constructor. auto. apply nal in H4. auto. 
    assert (a<>alloc). intro eq. assert (In alloc (a :: zs)). constructor. auto. apply nal2 in H5. auto. 
    rewrite <- H2. rewrite <- H3. simpl.
    unfold readvar. ne H4. ne H5. simpl.
    case_eq(Nat.eq_dec a x );intros. assert (In x (a :: zs)). simpl. left;auto. apply nal3 in H7;contradiction.
    pose (eqe 0) as eqe'. simpl in eqe'.
    rewrite eqe'. apply veqrefl. lia.
  ---
    destruct H2.
    inversion H. apply IHzs with (s:=s) (t:=t) (x:=x) in H5;auto. unfold state_resp_sub in H5.
    assert (v<>alloc).  admit. 
    unfold readvar.  ne H4.  
    unfold readvar in H5. 
    assert (NM.find (elt:=pureexprd) v (⇑ₘ combine (ret :: params) (map varpexpr (x :: zs))) = Some e ). apply NM.find_1.
    apply NM_.add_mapsto_iff. right. simpl. constructor;auto.  
    apply H5 in H6. nein H4 H6. apply H6.
    intros. apply (eqe (S i)). simpl. lia. 
    admit.
    admit.
    admit.
Admitted. *)
Lemma dom_list: forall K V, dom_nm (⇑ₘ (combine K V)) = NS'.of_list K.
Admitted.
(*we can refer to alloc in specs, but it should not appear in argl*)



Program Definition convertl (R: dbexp) (C:classname) (q:methodname) (x y:var) (zs: list var) (dep: syn_not_dependent R ({· x ·} ⨥ alloc))
(leq: (Datatypes.length zs) = (Datatypes.length (argsl C q)))
(ninzs: ~ List.In alloc (x::y::zs))
(s: {v : state | ⟦((pre C q) {`⇑ₘ combine (this :: argsl C q) (map varpexpr (y:: zs)) `}β) <*>· R⟧𝚩  v})
: {v : state |  ⟦((pre C q) <*>· (R {`csub R (s.1.1)`}β))⟧𝚩  v}
:= exist _ ((s[{`! map (fun xe => (xe.1, Interpe xe.2 s)) (combine (this:: (argsl C q)) ((map evar (y::zs))))!`}])) _.
Next Obligation.
  intros. destruct s as [s sprop]. simpl sval.
  apply List.not_in_cons in ninzs. destruct ninzs as [_ ninzs].
  remember (combine (this:: (argsl C q)) (map varpexpr (y :: zs))) as subl. 
  remember ((pre C q) {` ⇑ₘ subl`}β) as pre'.
  remember (s [{`! map (fun xe => (xe.1, Interpe xe.2 s)) (combine (this:: (argsl C q)) ((map evar ((y :: zs))))) !`}]) as s'.
  assert (NS.mem alloc (fv R) = false). unfold syn_not_dependent in dep. apply NS_.not_mem_iff. NSDecide.fsetdec.
  assert ((⥙ R ⥕Β) s = (⥙ R {`csub R s.1.1 `}β ⥕Β) s'). pb. apply closingspfragb. apply exeqrefl. rewrite Heqs'. auto. auto.
  assert (fv (pre C q) ⊆ (NS'.of_list (this :: argsl C q) ⊍ ({·alloc·}))). apply fvpre. 
  assert (state_resp_sub s' s (⇑ₘ subl)). unfold state_resp_sub. rewrite Heqs'. rewrite Heqsubl. apply args_srs. apply fvargsl. apply ninzs. simpl;auto. 
  intros. apply trunc_in;simpl;auto. apply fvargsl. apply nodupargsl. 
  assert ((⥙ pre C q ⥕Β) s' = (⥙ pre' ⥕Β) s). pb. 
  erewrite pfragb_weakensub with (sub:=⇑ₘ subl);auto. 
  case_if. rewrite Heqs'. simpl. PSDecide.fsetdec.
  unfold exeqFull. constructor. rewrite Heqsubl. rewrite dom_list.
    (*no requirement for stack*) 
  apply exeqfsetsub with (A:=∅). NSDecide.fsetdec. (*can't pose fvp, pose fails fdec*) apply exeq_emp. 
  rewrite Heqs'. apply exeqhrefl.
  

  apply dbsat_def in sprop. destruct sprop as [okspec sprop]. destruct sprop as [Rok [dis1 sub1]].
  apply dbsat_def.
  constructor.
  -
    ib. ibin okspec.
    erewrite interpb_weakensub with (sub:=⇑ₘ subl);auto. rewrite Heqpre' in okspec. apply okspec.
    case_if. rewrite Heqs'. simpl. PSDecide.fsetdec.
    unfold exeqFull. constructor. rewrite Heqsubl. rewrite dom_list.
     (*no requirement for stack*) 
    apply exeqfsetsub with (A:=∅). NSDecide.fsetdec. (*can't pose fvp, pose fails fdec*) apply exeq_emp. 
    rewrite Heqs'. apply exeqhrefl. auto.
  -
  constructor. 
  --
    ib. erewrite <- closinginterpb;eauto. apply exeqrefl.
    rewrite Heqs'. simpl. auto.
  --
  constructor.
  ---
    rewrite <- H0. rewrite H3.  
    auto.
  ---
    rewrite <- H0. rewrite H3. rewrite Heqs'. auto.
Defined.


Program Definition convertl' (R: dbexp) (C:classname) (q:methodname) (x y:var) (zs: list var)
(s: {v : state | ⟦((pre C q) {`⇑ₘ combine (this :: (argsl C q)) (map varpexpr (y :: zs)) `}β) <*>· R⟧𝚩 v}) 
(dep: syn_not_dependent R ({· x ·} ⨥ alloc)) (leq: Datatypes.length zs = Datatypes.length (argsl C q)) (ninzs: ~ List.In alloc (x::y::zs))
(t: {v : state| ⟦((post C q) <*>· (R {`csub R (s.1.1)`}β))⟧𝚩 v /\
    eqexcept (modifies (getm (gamma C) q)) (γ` v) (Γ` convertl R C q x y zs dep leq ninzs s)})
(nofv: ~ List.In x (y::zs))
(not_modify_x: NS.Empty (NS.inter (⇑ₛ (this::argsl C q)) (modifies (getm (gamma C) q))))
: {v : state | ⟦(((post C q) {`⇑ₘ combine (ret :: this :: argsl C q) (map varpexpr (x:: y:: zs)) `}β) <*>· R)⟧𝚩 v /\ 
eqexcept ({· x ·} ⨥ alloc) (γ` v) (Γ` s)}
:= exist _ (substl s.1.1 [(x, (t.1.1 ret))], t.1.2, t.2) _.
Next Obligation.
  intros. destruct s as [s sprop]. destruct t as [t tprop]. destruct tprop as [tprop tp]. simpl sval in *. constructor.
  remember (s [{`! map (fun xe => (xe.1, Interpe xe.2 s)) (combine (this:: (argsl C q)) ((map evar ((y :: zs))))) !`}]) as s'.
  assert ((fv (post C q)) ⊆ (NS'.of_list (ret :: this :: argsl C q) ⊍ ({·alloc·}))) as fvpo. apply fvpost.
  unfold syn_not_dependent in dep. 
  assert (state_resp_sub t (substl s.1.1 [(x, t.1.1 ret)], t.1.2, t.2) (⇑ₘ combine (ret :: this :: argsl C q) (map varpexpr (x :: y :: zs)))).
  {
    apply args_srs;auto. apply List.not_in_cons. constructor. unfold alloc, ret. auto. apply fvargsl. simpl;auto.
    intros. destruct i. 
    --
      simpl. id x. auto.
    --
      unfold convertl in tp. unfold getstack' in tp. simpl sval in tp. rewrite nth_next. rewrite nth_next. 
      simpl in H. apply lt_S_n in H. 
      apply eq_trans with (s'.1.1 (nth i (this :: argsl C q) alloc)).
      ---
        unfold getstack in tp. unfold eqexcept in tp. rewrite Heqs'. apply tp.
        assert (NS.In (nth i (this :: argsl C q) alloc) (⇑ₛ (this :: argsl C q))). 
        apply NS'.of_list_1. assert (i< List.length (this :: argsl C q)). simpl. auto.
        apply In_InA;auto. 
        eapply List.nth_In in H0. apply H0.
        clear - not_modify_x H0. NSDecide.fsetdec.
      ---
        rewrite Heqs';auto.
        assert (i< List.length (y :: zs)). simpl. rewrite leq. auto.
        rewrite trunc_in;auto.
        assert ((substl s.1.1 [(x, t.1.1 ret)], t.1.2, t.2).1.1 = substl s.1.1 [(x, t.1.1 ret)]). auto. rewrite H1. rewrite substl_notin. auto.
        simpl split. simpl fst. 
        apply ninsing. apply nth_neq;auto. 
        apply fvargsl. apply List.not_in_cons in ninzs. destruct ninzs;auto. apply nodupargsl. simpl. auto.
  }
  assert (eqxcptS (substl s.1.1 [(x, t.1.1 ret)], t.1.2, t.2).1.1 s.1.1 (fv R)).
  {
    unfold eqxcptS. intros.
    assert ((substl s.1.1 [(x, t.1.1 ret)], t.1.2, t.2).1.1 = substl s.1.1 [(x, t.1.1 ret)]). auto. rewrite H1. 
    rewrite substl_notin. auto. 
    simpl. intro eq2. destruct eq2;try contradiction. rewrite <- H2 in H0. apply NS.mem_2 in H0. clear - H0 dep. NSDecide.fsetdec.
  }
  -
  apply dbsat_def in tprop. destruct tprop as [postok [Rok [postRdisj postRsub]]]. apply dbsat_def.
  constructor.
  --
    (*we don't subst alloc here, and the alloc is kept unchanged as t anyway.*)
    (*we just have to ensure that the t resps sub evaluated on t', and a trivial exeq condition*)
    ib. ibin postok.
    erewrite <- interpb_weakensub. apply postok. reflexivity.
    case_if.
    unfold exeqFull. constructor. rewrite dom_list. apply exeqfsetsub with (A:=∅). clear - fvpo. NSDecide.fsetdec. apply exeq_emp.
    apply exeqhrefl. apply H.
  --
  constructor.
  ---
    ib. ibin Rok.
    erewrite closinginterpb. apply Rok.
    simpl. auto. auto. apply NS_.not_mem_iff. clear - dep. NSDecide.fsetdec.
  ---
  constructor.
  ----
    pb. pbin postRdisj.
    erewrite <- pfragb_weakensub with (xd:= (post C q))(xdsub:=((post C q) {`⇑ₘ combine (ret :: this :: argsl C q) (map varpexpr (x :: y :: zs)) `}β)). erewrite closingspfragb with (xd:=R).
    apply postRdisj.
    auto. auto. apply NS_.not_mem_iff. clear - dep. NSDecide.fsetdec.
    reflexivity. 
    case_if. 
    unfold exeqFull. constructor. rewrite dom_list. apply exeqfsetsub with (A:=∅). clear - fvpo. NSDecide.fsetdec. apply exeq_emp.
    apply exeqhrefl. apply H.
  ----
      pb. pbin postRsub.
      erewrite <- pfragb_weakensub with (xd:= (post C q))(xdsub:=((post C q) {`⇑ₘ combine (ret :: this :: argsl C q) (map varpexpr (x :: y :: zs)) `}β)). erewrite closingspfragb with (xd:=R).
      apply postRsub.
      auto. auto. apply NS_.not_mem_iff. clear - dep. NSDecide.fsetdec.
      reflexivity. 
      case_if.
      unfold exeqFull. constructor. rewrite dom_list. apply exeqfsetsub with (A:=∅). clear - fvpo. NSDecide.fsetdec. apply exeq_emp.
      apply exeqhrefl. apply H.
  -
    unfold eqexcept. intros. unfold getstack. unfold getstack'. simpl. case_eq( Nat.eq_dec x0 x);intros;auto. 
    rewrite e in H. NSDecide.fsetdec.
Defined.

Definition split_dep_cmd {R:dbexp} {c1 c2: cmd} (dep0: syn_not_dependent R (modifies (seq c1 c2))): (syn_not_dependent R (modifies c1) * syn_not_dependent R (modifies c2)).
Admitted.
Definition split_eq {P Q} (t: {v: state| P v /\ Q v}): ({v': {v: state| P v} | Q (proj1_sig v')}).
Proof.
Admitted.
Program Definition seq' (c1 c2: cmd) (P QQ Q R: dbexp) (s: {v : state | ⟦(P <*>· R)⟧𝚩 v}) 
(t: {v' : {v : state | ⟦(QQ <*>· R)⟧𝚩 v}| eqexcept (modifies c1) (Γ` v') (Γ` s)})
(t2: {v : state | ⟦(Q <*>· R)⟧𝚩 v /\ eqexcept (modifies c2) (γ` v) (Γ` (proj1_sig t))})
:  {v : state | ⟦(Q <*>· R)⟧𝚩 v /\ eqexcept (modifies (seq c1 c2)) (γ` v) (Γ` s)}:= (exist _ t2 _).
Next Obligation.
  intros. destruct s as [s sprop]. destruct t as [[t tprop] teq]. destruct t2 as [t2 t2prop]. simpl in *. destruct t2prop as [t2prop t2eq].
  unfold getstack, getstack' in *. simpl in *.
  constructor;auto.
  unfold eqexcept in *. intros. 
  apply eq_trans with (t.1.1 x). apply t2eq. NSDecide.fsetdec. apply teq. NSDecide.fsetdec.
Defined.

Program Definition strengthen (P R: dbexp) (test: dbexp) (s: {v : state | ⟦(P <*>· R)⟧𝚩 v}) (ev: ⟦test⟧Β ( s)) (pt: pure test)
: {v : state | (⟦(test <*>· P) <*>· R⟧𝚩) v} := s.
Next Obligation.
  intros. destruct s as [s sprop]. simpl in *.
  apply dbsat_def in sprop. destruct sprop as [pok [rok [dis subs]]].
  apply dbsat_def.
  assert (PNS.Empty ((⥙ test ⥕Β) s));auto.
  constructor.
  -
  rewrite sc_def. apply andbb;auto. apply andbb;auto.
  unfold pure in pt. unfold pnsdisj in *. handle_sets. PNSDecide.fsetdec.
  -
  constructor;auto.
  constructor.
  --
  unfold pnsdisj in *. rewrite sc_pdef. handle_sets. PNSDecide.fsetdec.
  --
  rewrite sc_pdef. unfold pfrag in *. handle_sets. autorewrite with folddb in *.
  assert (PS.Empty (reduce ((⥙ test ⥕Β) s))). unfold reduce. apply PNS'.empty_is_empty_1 in H. 
  rewrite fold_equal_pns;eauto.
  rewrite PNS'.fold_empty. PSDecide.fsetdec. PSDecide.fsetdec. 
Defined.
Program Definition strengthen' (P R: dbexp) (test: dbexp)(s: {v : state | ⟦(P <*>· R)⟧𝚩 v}) (ev: ⟦test⟧Β ( s) = false)  (pt: pure test)
: {v : state | (⟦ ((dbnot test) <*>· P) <*>· R⟧𝚩) v} := s.
Next Obligation.
Admitted.
Program Definition eq_overapp1{P c1 c2 test prev} (s: {v: state| P v /\ eqexcept (modifies c1) (γ` v) prev}): ({v: state| P v /\ eqexcept (modifies (cond test c1 c2)) (γ` v) prev}) := s.
Next Obligation.
Admitted.
Program Definition eq_overapp2{P c1 c2 test prev} (s: {v: state| P v /\ eqexcept (modifies c2) (γ` v) prev}): ({v: state| P v /\ eqexcept (modifies (cond test c1 c2)) (γ` v) prev}) := s.
Next Obligation.
Admitted.

Lemma closingndp: forall R s C q, syn_not_dependent (R {`csub R (s)`}β)
  (modifies (getm (gamma C) q)).
Proof.
  intros. unfold syn_not_dependent.
  rewrite csub_fv2. NSDecide.fsetdec.
Defined.

Obligation Tactic := idtac; auto with *.

Equations interp'{c P Q}
(* {PA QA:exeassn}  *)
(step:nat) (good: hoare c P Q) R (dep: syn_not_dependent R (modifies c))
(s:{v:state|⟦(P <*>· R)⟧𝚩 v}) : option ({v:state|⟦(Q <*>· R)⟧𝚩 v /\ eqexcept (modifies c) (γ` v) (Γ` s)}) (*wired paraentness for parsing*):= 
(* (s:{v:state|(⟦ P ⟧β) v = true}) : option {v:state|(⟦ Q ⟧β) v = true} :=  *)
interp' 0 _ R dep _ := None;
interp' (S n) (HAssign2 e P a neq1 nin1 nin2 acc) R dep s := Some (f'' nin1 nin2 neq1 acc dep s);
interp' (S n) (HConseq c P Q P' Q' imp1 g imp2) R dep s := let t0 := (conseq P P' R imp1 s) in let t := (interp' n g R dep t0) in match t with | None => None | Some t' => Some (conseq' c Q' Q R imp2 ((Γ` t0)) t') end;
interp' (S n) (HFrame c P Q R' dep' g) R dep s := match (interp' n g (dbsc R' R) (merge_dep_assn dep' dep) (sc_assoc1 s)) with | None => None | Some ss => Some (trans' c Q R' R (Γ` s) ss) end;
interp' (S n) (HWrite f a e neq1 ip) R dep s := Some (write' neq1 ip s);
interp' (S n) (HNew D a oldalloc neq1 neq2 neq3) R dep s := Some (new' D a oldalloc R dep neq1 neq2 neq3 s);
interp' (S n) (HCall q x y zs C nofv noalloc leq) R dep s:= let t := interp' n (pok C q) (R {`csub R (proj1_sig s).1.1`}β) (closingndp R ((proj1_sig s).1.1) C q) (convertl R C q x y zs dep leq noalloc s) in match t with | None => None | Some t' => Some (convertl' R C q x y zs s dep leq noalloc t' nofv  (params_not_modified C q)) end;
interp' (S n) (HSeq c1 c2 P QQ Q g1 g2) R dep s := 
  let (dep1, dep2) := split_dep_cmd dep in 
  (*P * R -> QQ * R*)
  match (interp' n g1 R dep1 s) with |None => None 
  (*QQ * R -> Q * R = Q * R *)
  | Some t => let t' := split_eq t in match (interp' n g2 R dep2 (proj1_sig t')) with | None => None | Some t'' => Some (seq' c1 c2 P QQ Q R s t' t'') end end;
interp' (S n) (HCond test c1 c2 P Q pt g1 g2) R dep s :=
let (dep1, dep2) := split_dep_cmd dep in 
(match ⟦test⟧Β (proj1_sig s) as b return ⟦test⟧Β (proj1_sig s) = b -> option ({v:state|⟦(Q <*>· R )⟧𝚩 v  /\ eqexcept (modifies (cond test c1 c2)) (γ` v) (Γ` s)}) with
| true  => fun ev => let pv := proj2_sig s in match (interp' n g1 R dep1 (strengthen P R test s ev pt)) with | None => None | Some t => Some (eq_overapp1 t) end(*does not know about test s, only know b is true*)
| false => fun ev => let pv := proj2_sig s in match (interp' n g2 R dep2 (strengthen' P R test s ev pt)) with | None => None | Some t => Some (eq_overapp2 t) end
end) erefl. 


End CMDSems. 