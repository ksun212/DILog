
Require Import Coq.Lists.List.
Import ListNotations.
Require Import JavaHoareIDFAllDeepHoareFramedExplicit.
Definition List := 2.


Set Bullet Behavior "Strict Subproofs".
Module L <: Measures.
Lemma cneq1: List <> Object.
auto.
Defined.
Definition mappend : methodname := 2.
Definition ft : var := 10.
Definition oldalloc : var := 11.
Global Hint Unfold ft : namesdb.
Global Hint Unfold oldalloc : namesdb.
Goal ft <> xx1.
solve_names.
Defined.
Definition gamma: Program := 
  fun c => match Nat.eq_dec c List with 
  | (left _) => 
    (((fun p => match Nat.eq_dec p valid with
      | (left _) => 
          bif (((′ this) … (next)) ·=· (eval null))
          then 
            (b_ ((′ this)) `∈ ((′ this) … repr))
          else 
            bif (b_ ((′ this) … next) `∈ ((′ this) … repr))
            then 
              bif (b_ ((′ this) … next … repr) `⊂ ((′ this) … repr) </\>· (<!>  (b_ ((′ this)) `∈ ((′ this) … next … repr)))) 
              then 
                (b_ ((′ this)) `∈ ((′ this) … repr)) </\>· ((′ this) … (next) @ List ∥ cneq1 ⟼ valid ())
              else
                dbf
            else
              dbf
        | (right _) => 
            dbt 
        end), 
    (fun f => match Nat.eq_dec f length with
    | (left _) =>  (eval null)
    | (right _) => (eval null) end), 
              
    (fun m => match Nat.eq_dec m mappend with
    | (left _) => 
      xx1 `:= ((′ this) … next) ;;
      xx2 `:= ((′ this) … repr) ;;
      cif ((′ xx1) ·=· (! null))
      then {ᵪ
        ret `≔ List;; 
        ret `… next `:= (! null) ;;
        ret `… repr `:= ({ₛ (′ ret) ₛ});;
        this `… next `:= (′ ret);;
        this `… repr `:= (b' (′ xx2) `∪ ({ₛ (′ ret) ₛ}))
      }ᵪ
      else {ᵪ
        xx3 `:= ((′ xx1) … repr) ;;
        ret `⩴ xx1 ⟼ mappend (` (xx3) :: (oldalloc) :: nil`);;
        this `… repr `:= (b' (′ xx2) `∪ ({ₛ (′ ret) ₛ}))
      }ᵪ
    | (right _) => 
      skip
    end), 
    NS.add next (NS.singleton repr), Object)
    )
  | (right _) => 
      emptyclass 
  end.  
  Definition specs: specTable :=
  fun c =>  match Nat.eq_dec c List with 
  | left _ =>  
    (fun p => match Nat.eq_dec p valid with
    | left _ => (b' (u' `{}` (′ this)) `∪ (((′ this) … repr)))| right _ => (eval null) end, 
    fun m => if Nat.eq_dec m mappend then 
    (([ft;oldalloc]), 
    (
    (((′ ft) ·=· ((′ this) … repr)) </\>· 
    ((′ this) @ List ∥ cneq1 ⟼ valid ()) </\>· 
    (b_ ((′ this) … repr) `⊂ (′ oldalloc))) <*>·   
    (((′ oldalloc) ·=· (′ alloc))) <*>· 
    (b_ ((′ this)) `∈ (′ oldalloc)) <*>· 
    (b_ ((! null)) `∈ (′ oldalloc))
    ), 
    ((((b' (′ ft) `∪ ({ₛ (′ ret) ₛ})) ·=· ((′ this) … repr)) </\>· 
    ((′ this) @ List ∥ cneq1 ⟼ valid ())) <*>· 
    (b_ ({ₛ (′ ret) ₛ}) `!! (′ oldalloc))) )
    else (nil, ((′ this) @ List ∥ cneq1 ⟼ valid ()), dbt))    
  | right _ => 
    (fun p => (eval null), 
    fun m => (nil, dbt, dbt))
  end.


  Definition carrier := (classname * fname * val)%type.
  Definition lt2 := fun (c1 c2:carrier) => match natnat_DT.eq_dec ((Object, maine): (classname*fname)%type) c2.1 with | left _ => match natnat_DT.eq_dec ((Object, maine): (classname*fname)%type) c1.1 with | left _ => false | right _ => true end | right _ => false end .
  Program Definition mford:dec_strorder := Build_dec_strorder carrier lt2.
  Definition mf (f : classname * fname * state) := (f.1, vint 0).
  Definition call_ordere := (fun x y : classname * fname * state => (dso_ltb mford (mf x) (mf y))).
  Lemma wfe:  well_founded call_ordere.
  Proof.
  unfold well_founded. intros.
  apply Acc_intro. intros.
  unfold call_ordere in H. simpl in H. unfold lt2 in H. 
  case_eq(PSDecide.F.eq_dec (Object, maine) (mf a).1);intros. rewrite H0 in H. 
  case_eq(PSDecide.F.eq_dec (Object, maine) (mf y).1);intros. rewrite H1 in H. inversion H.
  apply Acc_intro. intros. unfold call_ordere in H2. simpl in H2.  unfold lt2 in H2. rewrite H1 in H2. inversion H2.
  rewrite H0 in H. inversion H.
  Defined.

  Definition carrier2 := (classname * pname * val)%type.
  Definition lt1_b (c: (classname * pname)%type) := 
  match (natnat_DT.eq_dec c (Object, mainb)), (natnat_DT.eq_dec c (List, valid)) with 
  | (left _), _ => 2
  | (right _), (left _)  => 1 (**)
  | _, _ => 0
  end.
  Definition lt1b (c1 c2: (classname * pname)%type) := 
  Nat.ltb (lt1_b c1) (lt1_b c2).
  Definition ltval(v1 v2: val) :=
    match v1, v2 with 
    | (vint n1), (vint n2) => Nat.ltb n1 n2
    | (vptr p1), (vptr p2) => Nat.ltb p1.1 p2.1
    | (vset s1), (vset s2) => compssubset s1 s2
    | _, _ => false
    end.
    
  Definition lt2b (c1 c2: (classname * pname * PS.t)%type) := 
  (*the right side is _, then must not lt*)
  match natnat_DT.eq_dec c2.1 (Object, mainb), natnat_DT.eq_dec c2.1 (List, valid) with
  | (right _), (right _) => false 
  | _, _ => 
  (*the left side is _, then must lt*)
  match natnat_DT.eq_dec c1.1 (Object, mainb), natnat_DT.eq_dec c1.1 (List, valid) with
  | (right _), (right _) => true 
  | _, _ => 
  (*left and right side is not _, if not equal, test depth, else test val*)
  match natnat_DT.eq_dec c1.1 c2.1 with 
  | left _ => compssubset c1.2 c2.2
  | right _ => lt1b c1.1 c2.1
  end end end.
  Program Definition mdbord:dec_strorder := Build_dec_strorder (classname * pname * PS.t)%type lt2b.
  Definition m (f : classname * pname * state) := 
  match natnat_DT.eq_dec f.1 (List, valid), natnat_DT.eq_dec f.1 (Object, mainb) with 
  | (left _), _ => (List, valid, (val_to_set ((f.2.1.2 (val_to_ptr (f.2.1.1 this), repr)))))
  | (right _), (left _) => (Object, mainb, PS.empty)
  | _, _ => (f.1, PS.empty)
  end.
  Definition call_order := (fun x y : classname * pname * state => (dso_ltb mdbord (m x) (m y))).


  Lemma wfm:  well_founded call_order.
  unfold well_founded. intros. 
  assert (forall p s, (exists tmp1 tmp2, (natnat_DT.eq_dec p (List, valid) = (right tmp1) /\ natnat_DT.eq_dec p (Object, mainb) = (right tmp2))) -> Acc (fun x y : classname * pname * state => call_order x y) (p, s)).
  intros. destruct H as [tmp1[tmp2 [H H0]]]. 
  apply Acc_intro. intros. unfold call_order in H1. simpl in H1. unfold lt2b in H1. unfold m in H1. simpl in H1.
  rewrite H in H1. rewrite H0 in H1. simpl in H1. rewrite H in H1. rewrite H0 in H1. inversion H1.

  assert (forall p s, (exists tmp1, (natnat_DT.eq_dec p (List, valid) = (left tmp1) )) -> Acc (fun x y : classname * pname * state => call_order x y) (p, s)).
  intros. destruct H0 as [tmp1 H0].
  remember (val_to_set ( (s.1.2 (val_to_ptr (s.1.1 this), repr)))) as n;intros.
  assert (p = (List, valid)). auto. rewrite H1. clear H1.
  (*do induction on the "coerced" n, another Facter valid will also get a "coerced" n.*)
  generalize dependent s. generalize dependent n.
  apply (well_founded_induction wf_strict_subset' (fun n => forall (s : state), n =  val_to_set ( (s.1.2 (val_to_ptr (s.1.1 this), repr))) ->
  Acc  (fun x y : classname * pname * state => call_order x y) ((List, valid), s)));intros. 
  apply Acc_intro. intros. destruct y as [p1 s1]. unfold call_order in H3. unfold m in H3. simpl in H3. 
  case_eq(natnat_DT.eq_dec p1 (List, valid));intros. unfold lt2b in H3. rewrite H4 in H3. simpl in H3.
  apply cssub_ssub in H3. simpl in H2. rewrite <- H2 in H3. pose (H1 (val_to_set ( (s1.1.2 (val_to_ptr (s1.1.1 this), repr)))) H3 s1) as HH1. assert (p1 = (List, valid)). auto. rewrite H5. clear H5. apply HH1. auto.
  case_eq(natnat_DT.eq_dec p1 (Object, mainb));intros. unfold lt2b in H3. rewrite H4 in H3. rewrite e in H3. simpl in H3. unfold lt1b, lt1_b in H3. simpl in H3. inversion H3.
  assert ((exists tmp1 tmp2, natnat_DT.eq_dec p1 (Facter, valid) = right tmp1 /\ natnat_DT.eq_dec p1 (Object, mainb) = right tmp2)). exists n. exists n0. auto.
  apply (H p1 s1) in H6. apply H6.



  assert (forall p s, (exists tmp1, (natnat_DT.eq_dec p (Object, mainb) = (left tmp1) )) -> Acc (fun x y : classname * pname * state => call_order x y) (p, s)).
  intros. destruct H1 as [tmp1 H1]. 
  apply Acc_intro. intros. unfold call_order in H2. simpl in H2. unfold lt2b in H2. unfold m in H2. simpl in H2.
  rewrite H1 in H2. rewrite tmp1 in H2. simpl in H2. unfold lt1b in H2. unfold lt1_b in H2.
  destruct y as [p1 s1]. simpl in H2.
  case_eq(natnat_DT.eq_dec p1 (List, valid));intros. rewrite H3 in H2. simpl in H2.
  assert ((exists tmp1, natnat_DT.eq_dec p1 (List, valid) = left tmp1)). exists e. auto. 
  apply (H0 p1 s1) in H4. auto.
  case_eq(natnat_DT.eq_dec p1 (Object, mainb));intros. rewrite H4 in H2. rewrite e in H2. simpl in H2. unfold Nat.ltb in H2;inversion H2.
  assert ((exists tmp1 tmp2, natnat_DT.eq_dec p1 (List, valid) = right tmp1 /\ natnat_DT.eq_dec p1 (Object, mainb) = right tmp2)). exists n. exists n0. auto.
  apply (H p1 s1) in H5. apply H5.

  destruct a.
  case_eq(natnat_DT.eq_dec p (List, valid));intros. assert (exists tmp1, natnat_DT.eq_dec p (List, valid) = left tmp1). exists e. auto. apply (H0 p s) in H3. auto.
  case_eq(natnat_DT.eq_dec p (Object, mainb));intros. assert (exists tmp1, natnat_DT.eq_dec p (Object, mainb) = left tmp1). exists e. auto. apply (H1 p s) in H4. auto.
  assert ((exists tmp1 tmp2, natnat_DT.eq_dec p (Facter, valid) = right tmp1 /\ natnat_DT.eq_dec p (Object, mainb) = right tmp2)). exists n. exists n0. auto. apply (H p s) in H4. apply H4.
  Defined.


  Definition carrierm := (classname * methodname * val)%type.
  Definition lt2m := fun (x y:carrierm) => false.
  Program Definition mmethod:dec_strorder := Build_dec_strorder carrierm lt2m.
  Definition mm (f : classname * methodname * state) := (f.1, vint 0).
  Definition call_orderm := (fun x y : classname * methodname * state => (dso_ltb mmethod (mm x) (mm y))).
  Lemma wfmm:  well_founded call_orderm.
  Proof.
  unfold well_founded. intros.
  apply Acc_intro. intros. unfold call_ordere in H. simpl in H. unfold lt2 in H. inversion H.
  Defined.
End L. 

Module L0 <: PWF L.
  Module M := BTSems L.
  Import M.
  Import L.
  Program Definition faa' C p (s: state): (wlpe C p (s) (getfun (gamma C) p)) (s).
  Proof.
    case_eq (Nat.eq_dec C List);intros. 
    -
    unfold getfun. unfold gamma. rewrite H. simpl. 
    case_eq (Nat.eq_dec p length);intros. 
    --
    simpl. auto.
    --
    simpl. auto.
    -
    unfold getfun. unfold gamma. rewrite H. simpl. auto. 
  Defined.
  Lemma mainfreee: forall c sig, (wlpe Object maine sig c) sig.
  Proof.
    induction c;simpl;auto. 
    - intros. 
    unfold lt2. unfold mf. simpl fst. 
    case_eq(natnat_DT.eq_dec (Object, maine) (Object, maine));intros. 
    case_eq(natnat_DT.eq_dec (Object, maine) (c, f));intros. unfold natnat_DT.eq in e0. inversion e0. rewrite H2 in n. contradiction.
    auto.
    unfold natnat_DT.eq in n0. contradiction.
    - intros. unfold Disj. unfold Conj. case_eq((⟦ d ⟧β) sig );intros. rewrite IHc1. auto. unfold Not. rewrite H. rewrite IHc2. auto.
    - intros. unfold Conj. rewrite IHc1. rewrite IHc2. auto.
  Defined.
End L0.
Module L1 <: PWF0 L L0.
Module MM := ExprSems L L0.
Import MM.M.
Import MM.
Import L.
Import L0.
  Lemma directimp: forall C p s, (wlpdb C p s (getp (gamma C) p)) s.
  Proof.
    intros.
    case_eq (Nat.eq_dec C List);intros. 
      -
      unfold getp. unfold gamma. rewrite H. simpl. 
      case_eq (Nat.eq_dec p valid);intros.
      simpl.
      unfold Disj. simpl.
      case_eq( veq (s.1.2 (val_to_ptr (readvar s this), next)) null);intros.
      +
      apply orb_true_iff. left. unfold Conj. unfold teassn. rewrite H1. simpl. auto.
      +
      apply orb_true_iff. right. unfold Conj. unfold Not. rewrite H1. simpl. 
      case_eq (bops `∈ (s.1.2 (val_to_ptr (readvar s this), next)) (s.1.2 (val_to_ptr (readvar s this), repr)));intros.
      ++
      apply orb_true_iff. left.
      case_eq((bops `⊂ (s.1.2 (val_to_ptr (s.1.2 (val_to_ptr (readvar s this), next)), repr)) (s.1.2 (val_to_ptr (readvar s this), repr)))  &&
 (negb (bops `∈ (readvar s this) (s.1.2(val_to_ptr (s.1.2 (val_to_ptr (readvar s this), next)),  repr))))) ;intros.
      +++
      apply orb_true_iff. left. simpl. rewrite e. rewrite e0.
      unfold lt2b. simpl.
      unfold bops in H3. simpl in H3. apply andb_prop in H3. destruct H3. unfold liftsubset in H3. unfold Interpe. rewrite interpe_equation_2. rewrite interpe_equation_1. auto.
      +++
      simpl. unfold teassn. auto.
      ++
      simpl. unfold teassn. auto.
      +
      simpl. unfold teassn. auto.
      -
      unfold getp. unfold gamma. rewrite H. simpl.  unfold teassn. auto.
  Defined.

  Lemma mainfree: forall c sig, (wlpdb Object mainb sig c) sig.
  Proof.
    induction c;simpl;auto. 
    - intros. 
    case_eq(natnat_DT.eq_dec(c, p) (List, valid));intros. unfold lt2b. simpl. unfold m.  rewrite e0 . simpl. unfold lt1b. unfold lt1_b. simpl.   unfold Nat.ltb. auto. 
    case_eq(natnat_DT.eq_dec(c, p) (Object, mainb));intros. unfold lt2b. simpl. unfold m.  simpl in e0. inversion e0. contradiction.
    unfold m. simpl fst. rewrite H. rewrite H0. simpl. unfold lt2b. simpl fst. rewrite H. rewrite H0. simpl. auto.
    - intros. unfold Conj. rewrite IHc1. rewrite IHc2. auto.
    - intros. unfold Conj. rewrite IHc1. rewrite IHc2. auto.
    - intros. unfold Disj. unfold Conj. case_eq((⟦ c1 ⟧β) sig );intros. rewrite IHc1. rewrite IHc2. auto. unfold Not. rewrite H. rewrite IHc1. rewrite IHc3. auto.
  Defined.
  Lemma alloc_fun: forall D g A, NS.mem alloc ((fve (getfun (gamma D) g)) ⨪ A) = false.
  Proof.
    intros. 
    case_eq (Nat.eq_dec D List);intros.
    -
      unfold getfun. unfold gamma. rewrite H. simpl. 
      case_eq (Nat.eq_dec g length);intros.
      simpl. apply NS_.not_mem_iff. NSDecide.fsetdec.
      simpl. apply NS_.not_mem_iff. NSDecide.fsetdec.
    -
      unfold getfun. unfold gamma. rewrite H. simpl.
      simpl. apply NS_.not_mem_iff. NSDecide.fsetdec.
  Defined.
  Lemma alloc_pred: forall D g A, NS.mem alloc ((fv (getp (gamma D) g)) ⨪ A) = false.
  Proof.
    intros.
    case_eq (Nat.eq_dec D List);intros.
    -
      unfold getp. unfold gamma. rewrite H. simpl. 
      case_eq (Nat.eq_dec g valid);intros.
      simpl. apply NS_.not_mem_iff. assert (this<>alloc). unfold this, alloc;simpl;auto. NSDecide.fsetdec.
      simpl. apply NS_.not_mem_iff. NSDecide.fsetdec.
    -
      unfold getp. unfold gamma. rewrite H. simpl.
      simpl. apply NS_.not_mem_iff. NSDecide.fsetdec.
  Defined.
  Lemma predfv: forall D g, ((fv (getp (gamma D) g))) ⊆ {·this·} .
  Proof.
    intros.
    case_eq (Nat.eq_dec D List);intros.
    -
      unfold getp. unfold gamma. rewrite H. simpl. 
      case_eq (Nat.eq_dec g valid);intros.
      simpl. NSDecide.fsetdec.
      simpl. NSDecide.fsetdec.
    -
      unfold getp. unfold gamma. rewrite H. simpl.
      simpl. NSDecide.fsetdec.
  Defined.
End L1.
Module L2 <: PWF1 L L0 L1.
Module BTH := BTSemsHoare L L0 L1.
  Import L1.MM.
  Import L1.MM.M.
  
  Import BTH.
  Import L.
  Import L0.
  From Equations Require Import Equations.
  
  Lemma reduce_if: forall (test:bool) A B, reduce (if test then A else B) = if test then reduce A else reduce B.
  Admitted.
  Global Hint Rewrite reduce_if: folddb.
  Global Hint Rewrite reduce_empty: folddb.
  Global Hint Rewrite reduce_union: folddb.
  Lemma testind: forall(ck: classname * pname * state * dbexp) sp, ck.2 = ((getp (gamma List) valid)) -> PS.Subset (reduce (pfragb ck.1.1.1 ck.1.1.2 ck.2 ck.1.2 sp)) (val_to_set (⟦((specs List).1 valid)⟧Ε ck.1.2)).
  Proof.
    apply (well_founded_ind order_wf (fun ck => forall(sp : wlpdb ck.1.1.1 ck.1.1.2 ck.1.2 ck.2 ck.1.2),
    ck.2 = getp (gamma List) valid -> PS.Subset (reduce (pfragb ck.1.1.1 ck.1.1.2 ck.2 ck.1.2 sp)) (val_to_set (⟦((specs List).1 valid)⟧Ε ck.1.2))));intros.
    destruct x as [[[xc xp] s] xd]. simpl in *. unfold getp, gamma in H0. simpl in H0. subst xd.
    rewrite pfragb_nodepwp'. autorewrite with esemdb. simpl. unfold readvar. unfold bops. autounfold with dbops. simpl. 
    case_eq( s.1.2 (↓ₚ s.1.1 this, next) `= null);intros.
    -
      autorewrite with folddb. simpl. PSDecide.fsetdec.
    -
      case_eq(PS.mem (↓ₚ s.1.2 (↓ₚ s.1.1 this, next)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)));intros.
      --
        autorewrite with folddb. simpl.
        case_eq(PS.subset (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) &&
                ~~ PS.equal (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) &&
                ~~  PS.mem (↓ₚ s.1.1 this) (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)));intros.
        ---
          simpl.
          pb. pe. ie. autorewrite with folddb. 
          (* set (ss := (s[{`![(this, interpe Object maine (  (′ this)  … next) s (mainfreee (  (′ this)  … next) s))]!`}])). *)
          assert (order (List, valid, (s[{`![(this, (⟦  ( ′ this ) … next ⟧Ε) s)]!`}]),  getp (gamma List) valid)
            (xc, xp, s,
            bif (  (′ this)  … next) ·=·  (! null)  then( b_ ( ′ this ) `∈ (  (′ this)  … repr))
            else bif b_ (  (′ this)  … next) `∈ (  (′ this)  … repr)
                  then bif (b_ (   (′ this)  … next … repr) `⊂
                            (  (′ this)  … repr) </\>·  (<!> b_ ( ′ this ) `∈ (   (′ this)  … next … repr)))
                      then   ( b_ ( ′ this ) `∈ (  (′ this)  … repr)) </\>· ((′ this)  … next @ List ∥ cneq1 ⟼ valid ())
                      else ⊥  else ⊥  )). apply left_lex.    
          simpl in sp. unfold Disj, Conj, Not, teassn in sp. simpl in sp. unfold readvar in sp. autounfold with dbops in sp. simpl in sp. rewrite H0, H1, H2 in sp. simpl in sp.
          unfold call_order. simpl. rewrite orb_rfalse in sp. rewrite orb_rfalse in sp. auto.
          apply H with (sp:=(L1.directimp List valid s[{`![(this, (⟦  ( ′ this ) … next ⟧Ε) s)]!`}])) in H3. simpl in H3. autorewrite with esemdb in H3. 
          (*this seems to be a wired bug of Equations that we are forced to rewrite back*)autounfold with dbops in H3. simpl in H3. iein H3. unfold readvar in H3. simpl in H3. 
          clear - H1 H2 H3. repeat destruct_andb. repeat handle_notb. handle_sets. apply PS_.not_mem_iff in H4. apply PS.mem_2 in H1.
          clear - H1 H2 H3. simpl.  
          PSDecide.fsetdec. simpl. auto.
        ---
          apply PS.mem_2 in H1.
          autorewrite with folddb. simpl. PSDecide.fsetdec.
      --
        autorewrite with folddb. simpl. PSDecide.fsetdec.
  Defined.
  Lemma predok: forall C p, exsub (getp (gamma C) p) ((specs C).1 p).
  Proof.
    intros.
    case_eq (Nat.eq_dec C List);intros.
    -
      unfold getp. unfold specs. unfold gamma. rewrite H. simpl.
      case_eq(Nat.eq_dec p valid);intros.
      +
      unfold exsub. intros.
      pose (testind (Object, mainb, s, (getp (gamma List) valid))). unfold getp, gamma in s0. simpl in s0.
      apply s0;auto.
      +
      unfold exsub. intros. unfold dbt. unfold Pfragb. rewrite pfragb_equation_1. autorewrite with interpe. unfold val_to_set. simpl.
      rewrite reduce_empty.
      PSDecide.fsetdec.
    -
      unfold getp. unfold specs. unfold gamma. rewrite H. simpl.
      unfold exsub. intros. unfold dbt. unfold Pfragb. rewrite pfragb_equation_1. autorewrite with interpe. unfold val_to_set. simpl.
      rewrite reduce_empty.
      PSDecide.fsetdec.
  Defined.
  (* Definition fsublemma (db:dbexp):= forall x (f:fieldname) s y, ⟦db⟧Β s -> ( (@PNS.singleton (val_to_ptr (s.1.1 x), f)) !! (⥙(dbsubst1f (db) x f (′ y))⥕Β s)).
  (*locally we must have z<> this for any z.f, globally we must have this not in any call*)
  Lemma fsubcomplete: forall C p x (f:fieldname) s y, ⟦(dbsubst1f ((getp (gamma C) p){( ′ x ) // this }β) x f (′ y))⟧Β s -> 
   ( (@PNS.singleton (val_to_ptr (s.1.1 x), f)) !! (⥙(dbsubst1f ((getp (gamma C) p){( ′ x ) // this }β) x f (′ y))⥕Β s)).
  Admitted. *)
  Definition splitsc (d:dbexp):=match d with | dbsc db1 db2 => Some (db1, db2) | _ => None end.
  Ltac printchunks := 
    match goal with
  | [d: dbexp |- _ ] =>
    let Cn1 := fresh "Chunk" in
    let Cn2 := fresh "Chunk" in
    let tmp := eval cbn in (splitsc d) in
    (lazymatch tmp with
    | Some (?c1, ?c2) =>
    set (Cn1 := c1);  set (Cn2 := c2); simpl in Cn1, Cn2; clear d
    | None =>
    fail "printchunks: cannot split"
    end) 
  end. 

  Ltac printchunks2 :=
  match goal with
  | [ d : dbexp |- _ ] =>
  let v := eval cbv in (splitsc d) in
  lazymatch v with
  | Some (?c1, ?c2) =>
  idtac "Chunk1 =" c1 "Chunk2 =" c2
  | None =>
  fail "printchunks: cannot split"
  end
  end.
  Ltac collect_precondition :=
  match goal with
  | [ |- hoare _ ?P _ ] =>
     let Pn := fresh "P" in
     set (Pn := P)
  | _ =>
     fail "collect_postcondition: goal is not of the form hoare _ P _"
  end.
  
  Ltac collect_postcondition :=
  match goal with
  | [ |- hoare _ _ ?Q ] =>
     let Qn := fresh "Q" in
     set (Qn := Q)
  | _ =>
     fail "collect_postcondition: goal is not of the form hoare _ _ Q"
  end.

  Ltac collect_db :=
  match goal with
  | [ |- is_true (interpb ?C ?P ?db ?s ?pf) ] =>
     let Qn := fresh "DB" in
     set (Qn := db)
  | _ =>
     fail "goal is not of the form"
  end.
  Ltac collect_dbin H:=
  match type of H with
  | is_true (interpb ?C ?P ?db ?s ?pf) =>
     let Qn := fresh "DB" in
     set (Qn := db)
  | _ =>
     fail "goal is not of the form"
  end.
  
  Ltac postR := 
    match goal with
  | [ |- hoare _ _ (?P1 </\>· ?P2)] =>
     let Rn := fresh "R" in
     set (Rn := P2)
  | _ =>
     fail "precondition is not of sc"
  end. 
  Ltac empE := 
    match goal with
  | [H: is_true (PNS.is_empty ?A) |- _ ] =>
     apply PNS.is_empty_2 in H
  | [ |- is_true (PNS.is_empty ?A) ] =>
    apply PNS.is_empty_1
  end. 
  
  Ltac rec_flatten_dbexp handler t :=
  lazymatch t with
  | dbsc ?A ?B =>
      (* split on dbsc at top level *)
      (lazymatch A with 
      | dbsc ?A' ?B' =>
        rec_flatten_dbexp handler A';
        rec_flatten_dbexp handler B'
      | _ => handler A 
      end);
      (lazymatch B with 
      | dbsc ?A' ?B' =>
        rec_flatten_dbexp handler A';
        rec_flatten_dbexp  handler B'
      | _ => handler B
      end)
  | dbconj ?A ?B =>
      rec_flatten_dbexp handler A;
      rec_flatten_dbexp handler B
  | _ => handler t
  end.

(* helper: make a fresh hypothesis binding the leaf *)
Ltac pose_leaf_as_var t :=
  let H := fresh "C" in
  pose (H := t).

(* wrapper: given a term of type dbexp, pose each leaf into the context *)
Ltac extract_db_components t :=
  rec_flatten_dbexp pose_leaf_as_var t.

  Lemma disunion: forall A B C, A !! B -> A !! C -> (A !! PNS.union B C).
  intros. unfold pnsdisj in *.
  repeat empE. PNSDecide.fsetdec.
  Defined.
  Lemma dissub: forall A B C, PS.Subset A B -> PS.Empty (PS.inter C B) -> PS.Empty (PS.inter C A).
  intros. PSDecide.fsetdec.
  Defined. 
  Lemma liftl: forall (f:fieldname) (r:ptr) A, (PS.singleton r) ! (reduce A) -> PNS.singleton (r, f) !! A.
  intros.
  unfold psdisj in H.
  assert ((r,f).1 = r). auto. rewrite <- H0 in H.
  rewrite <-reduce_singleton in H. 
  apply disj5 in H.
  unfold pnsdisj. handle_sets. auto.
  Defined.
  (*should annotate a b as ptr, otherwise sometimes inferred as ps.t, making the decision procedure fail*)
  Lemma liftlr: forall (f1:fieldname) (f2:fieldname) (a b: ptr), (PS.singleton a) ! (PS.singleton b) -> PNS.singleton (a, f1) !! PNS.singleton (b, f2).
  intros.
  unfold psdisj in H.
  assert ((a,f1).1 = a). auto. rewrite <- H0 in H.
  assert ((b,f2).1 = b). auto. rewrite <- H1 in H.
  
  rewrite <-reduce_singleton in H.
  rewrite <-reduce_singleton in H.
   
  apply disj5 in H.
  unfold pnsdisj. handle_sets.  auto.
  Defined.
  Definition Frame (p r p' : dbexp) :=
  p' <*>· r ⟺ p.
  Lemma FrameFound (p q r : dbexp)
  (H: p = r) :
  Frame (p <*>· q) r q.
  Admitted.
  Lemma FrameNotFound (p q r s : dbexp)
  (H: Frame q r s) :
  Frame (p <*>· q) r (p <*>· s).
  Admitted.
  Lemma FrameNotFoundConj (p q r s : dbexp)
  (H: Frame q r s)
   (Pu: pure p \/ pure q) :
  Frame (p </\>· q) r (p <*>· s).
  Admitted.
  Definition Pop (p r p' : dbexp) :=
  p' </\>· r ⟺ p.
  Lemma PopFound (p q r : dbexp)
  (H: p = r) :
  Pop (p </\>· q) r q.
  Admitted.
  Lemma PopNotFound (p q r s : dbexp)
  (H: Pop q r s) :
  Pop (p </\>· q) r (p </\>· s).
  Admitted.
  Ltac rewrite_esem_in H:= autorewrite with esemdb in H;simpl interpbbt in H;simpl interpebt in H;simpl pfragbbt in H;simpl pfragebt in H;unfold readvar in H.

  Lemma pok: forall C p, hoare (getm (gamma C) p) (pre C p) (post C p).
  Proof.
    intros.
    case_eq (Nat.eq_dec C List);intros.
    +
      unfold getm. unfold pre. unfold post. unfold specs. unfold gamma. rewrite H. simpl.
      case_eq(Nat.eq_dec p mappend);intros.
      ++
        simpl.
        eapply HSeq.
        *
          eapply HConseq.
          -
            eapply simptrans.
            apply iffimp1. apply siffsym.
            apply FrameFound. reflexivity.
            apply iffimp1.
            apply sccom.
          -
            apply HFrame.
            unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb. 
            apply HAssign2. solve_names. solve_names. auto 100 with nsdb. solve_names. auto 100 with nsdb.
            apply impacc. intros.
            rewrite_esem. simpl. rewrite unfoldpfrag;auto. unfold getp, gamma;simpl. rewrite bif_pdef. 
            case_eq(⟦ ( ( ′ this ) … next) ·=· ( ! null ) ⟧β s); intros;rewrite_esem; simpl; handle_sets; PNSDecide.fsetdec.
          -
            apply simprefl.
        *
        eapply HSeq.
        **
          eapply HConseq.
          -
            eapply simptrans.
            apply iffimp1. apply siffsym.
            apply FrameFound. reflexivity.
            apply iffimp1. apply sccom.
          -
            apply HFrame.
            unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb. 
            apply HAssign2. solve_names. solve_names. auto 100 with nsdb. solve_names. auto 100 with nsdb.
            apply impacc. intros.
            rewrite_esem. simpl. PNSDecide.fsetdec. 
          -
            apply simprefl.
        **
        apply HCond. unfold pure. intros. rewrite_esem. pe. PNSDecide.fsetdec. 
        ***
          eapply HSeq.
          *****
            eapply HConseq.
            -
            eapply simptrans.
            apply iffimp1. apply siffsym.
            apply FrameNotFound. apply FrameNotFound. apply FrameFound. reflexivity.
            apply iffimp1. apply sccom.
            -
            eapply HFrame.
            unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb.  
            apply HNew. solve_names. solve_names. solve_names.
            -
            eapply simptrans.
            eapply simptrans.
            apply scImp1.
            apply scImp1.
            unfold init. unfold getf. simpl. rewrite fold_add_init. rewrite fold_equal_init with (s' := (NS.add repr NS.empty)).
            rewrite fold_add_init. rewrite NS'.fold_empty. 
            apply scImp1.  apply simprefl. apply scImp2.
            NSDecide.fsetdec.
            NSDecide.fsetdec. solve_names. auto 100 with nsdb. 
            apply simprefl.
            apply simprefl.
            apply scass2. 
            apply scass2. 
          *****
          eapply HSeq.
          ******
            apply HFrame.
            unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb.  
            apply HWrite. solve_names. unfold pureexp. intros. pe. auto. 
          ******
          eapply HSeq.
          *******
            eapply HConseq.
            -
              eapply simptrans.
              apply iffimp1. apply siffsym.
              apply FrameNotFound. apply FrameFound. reflexivity.
              apply iffimp1. apply sccom.
            -
              eapply HFrame.
              unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb.  
              apply HWrite. solve_names. unfold pureexp. intros. pe. auto. 
            -
              apply simprefl.
          *******
          eapply HSeq.
          ********
            eapply HConseq.
            -
              eapply simptrans.
              apply iffimp1. apply siffsym.
              apply FrameNotFound. apply FrameNotFound. apply FrameNotFound. apply FrameNotFound. apply FrameFound. reflexivity.
              apply iffimp1. apply sccom.
            -
              eapply HFrame.
              unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb.  
              eapply HConseq.
              --
                eapply simptrans.
                ---
                  (*unfold*)
                  eapply conjImp1. apply simprefl.
                  eapply conjImp1. apply simprefl.
                  eapply conjImp1. apply simprefl.
                  eapply conjImp1. apply unfoldSImp. solve_names. apply simprefl.
                ---
                  eapply simptrans.
                  ----
                    eapply simptrans.
                    -----
                    (*pop1*)
                    apply iffimp1. apply siffsym.
                    apply PopNotFound. apply PopFound. reflexivity.
                    -----
                    (*pop2*)
                    apply conjcom.
                  ----
                    (*dump*)
                    apply prepare_write. intros. unfold pnsdisj. handle_sets. simpl. rewrite_esem. simpl.
                    case_eq(s.1.1 xx1 `= null);intros. solve_names. admit. admit.  
                    (* assert ((↓ₚ s.1.1 1, 2) <> (↓ₚ s.1.1 1, 3)). intro. inversion H3. auto. *)
              --
              apply HFrame. unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb.  
              apply HWrite. solve_names. unfold pureexp. intros. pe. auto. 
              --
              apply simprefl.
            -
              eapply simptrans. apply scass2.
              simpl dbsubst1f.
              apply simprefl.
          ********
            eapply HConseq.
            -
              eapply simptrans.
              --
              (*pop1*)
              apply iffimp1. apply siffsym.
              apply FrameNotFound. apply FrameFound. reflexivity.
              --
              (*pop2*)
              apply iffimp1. apply sccom.
            -
            eapply HFrame. unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb.
            eapply HConseq.
            apply prepare_write. admit.
            apply HFrame. unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb. 
            apply HWrite. solve_names. unfold pureexp. intros. pe. admit.
            apply simprefl.
            -
              apply simptrans with ((((b' ( ′ ft ) `∪ ({ₛ ′ ret ₛ}) ·=· ( ( ′ this ) … repr)) </\>·
              (( ′ this ) @ List ∥ cneq1 ⟼ valid ())) </\>· b_ ({ₛ ′ ret ₛ}) `!! ( ′ oldalloc ))).
              --
              apply conjintro.
              ---
                apply conjintro.
                ----
                  simpl dbsubst1f.
                  unfold Imp. intros. apply impbb. intros. apply andbb.
                  rewrite_esem_in H1. simpl in H1. repeat destruct_andb. 
                  
                  rewrite_esem. handle_notb. handle_bops.
                  apply veqsym. apply veqtrans with (ebops `∪ (s.1.1 xx2) (euops `{}` (s.1.1 ret))). solve_names. 
                  unfold veq. autounfold with dbops. simpl. apply veqseq in H14. apply PS.equal_1. apply PS.equal_2 in H14. PSDecide.fsetdec.
                  rewrite_esem. apply PNS.subset_1. PNSDecide.fsetdec.
                ----
                  simpl dbsubst1f.
                  unfold Imp. intros. apply impbb. intros. apply andbb.
                  -----
                    rewrite_esem_in H1. simpl in H1. repeat destruct_andb.
                    rewrite pcall_def.
                    unfold gamma. unfold getp. simpl.
                    rewrite_esem. simpl. unfold bops. autounfold with dbops. simpl. 
                    case_eq (s.1.2 (↓ₚ s.1.1 this, next) `= null);intros.
                    ------
                      handle_notb. handle_bops.
                      clear - H2 H13 H9 H8.
                      apply PS_.not_mem_iff in H8.  
                      apply veqpeq in H13. 
                      apply veqpeq in H2.
                      rewrite_esem_in H2. simpl in H2. rewrite H2 in H13. rewrite <- H13 in H8.
                      apply PS.mem_2 in H9. simpl in H9. apply H8 in H9. contradiction. 
                    ------
                      case_eq (PS.mem (↓ₚ s.1.2 (↓ₚ s.1.1 this, next)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)));intros.
                      -------
                        case_eq (PS.subset (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) && 
                        ~~ PS.equal (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) && ~~ PS.mem (↓ₚ s.1.1 this) (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)));intros.
                        --------
                          apply andbb.
                          ---------
                            clear - H6 H15 H18.
                            assert (s.1.1 xx1 `= null). apply H6.
                            rewrite H in H15.
                            apply veqseq in H18. apply PS.equal_2 in H18. rewrite H18.
                            apply PS.mem_1. autounfold with dbops in H15. autounfold with dbops. simpl in *. apply PS.mem_2 in H15. PSDecide.fsetdec.
                          ---------
                            rewrite pcall_def.
                            unfold gamma. unfold getp. simpl. 
                            rewrite_esem. simpl.
                            case_eq (s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), next) `= null);intros.
                            ----------
                              handle_bops. 
                              clear - H13 H12.
                              apply veqpeq in H13. apply veqseq in H12. simpl in *.
                              rewrite H13. apply PS.equal_2 in H12. rewrite H12. apply PS.mem_1.
                              autounfold with dbops. PSDecide.fsetdec.
                            ----------
                              clear - H13 H12 H21 H4. 
                              (* simpl in H27. iein H4. iein H6. iein H8. iein H27. unfold state_trunc in H27. simpl in H27. *)
                              apply veqpeq in H13.  rewrite H13 in H21. rewrite H4 in H21. inversion H21. 
                        --------
                        admit.
                      -------
                        admit.
                  -----
                    admit.
              ---
                eapply simptrans. apply scImp3.
                (*do a semantic proof, where actually reduces to another syntactical decision procedure*)
                unfold Imp. intros. apply impbb. intros. apply andbb.
                rewrite_esem_in H1. repeat destruct_andb. handle_notb. handle_bops.
                apply PS_.not_mem_iff in H15. rewrite_esem. autounfold with dbops. simpl. apply PS.is_empty_1. PSDecide.fsetdec.
                rewrite_esem. apply PNS.subset_1. PNSDecide.fsetdec.
            --
              apply conjsc.
              right. unfold pure. intros. rewrite_esem. PNSDecide.fsetdec. 
      ***
        eapply HSeq.
        ****
          eapply HConseq.
          *****
            eapply simptrans.
            apply iffimp1. apply siffsym.
            apply FrameNotFound. apply FrameFound. reflexivity.
            apply iffimp1. apply sccom.
          *****
            apply HFrame. 
            unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb. 
            apply HAssign2. solve_names. solve_names. auto 100 with nsdb. solve_names. auto 100 with nsdb.
            apply impacc. 
            admit.
            (* intros. rewrite_esem. simpl. rewrite_esem_in H1. repeat destruct_andb. simpl in *.
            apply veqpeq in H1. rewrite H1. rewrite unfoldpfrag;auto. rewrite_esem. unfold getp, gamma;simpl. 
            rewrite_esem. simpl. *)
          *****
            apply simprefl.
        ****
        eapply HSeq.
        *****
          (*we should copy some pure parts before frame*)
          (*we should do frame to keep as much info as possible*)
          eapply HConseq with (P':= (((( ′ xx3 ) ·=· ( ( ′ xx1 ) … repr)) </\>·
          ( ( ′ xx1 ) @ List ∥ cneq1 ⟼ valid ()) </\>·
          b_ ( ( ′ xx1 ) … repr) `⊂ ( ′ oldalloc )) <*>·
          (( ′ oldalloc ) ·=· ( ′ alloc )) <*>·
          b_ ( ′ xx1 ) `∈ ( ′ oldalloc ) <*>·
          b_ ( ! null ) `∈ ( ′ oldalloc )) <*>· 

          (((( ′ xx2 ) ·=· ( ( ′ this ) … repr)) </\>·
          (( ′ xx1 ) ·=· ( ( ′ this ) … next)) </\>·
          (( ′ ft ) ·=· ( ( ′ xx2 ))) </\>·  
          (b_ ((′ xx1)) `∈ ((′ xx2))) </\>· 
          (b_ ((′ xx3)) `⊂ ((′ xx2)) </\>· (<!>  (b_ ((′ this)) `∈ ((′ xx3))))) </\>· 
          b_ ( ( ′ xx2 )) `⊂ ( ′ oldalloc ) </\>· 
          (b_ ((′ this)) `∈ ((′ xx2)))
          ) <*>· 
          (<!> (( ′ xx1 ) ·=· ( ! null ))) <*>·
          b_ ( ′ this ) `∈ ( ′ oldalloc ) <*>·
          b_ ( ! null ) `∈ ( ′ oldalloc ))). 
          -
            (*unfold*)
            eapply simptrans.
            --
            apply scImp1. apply conjImp1. apply simprefl. apply conjImp1. apply simprefl. apply conjImp1. apply simprefl. apply conjImp1. apply simprefl.
            apply conjImp1. apply unfoldSImp;auto. apply simprefl. apply simprefl.
            --
            unfold Imp. intros. apply impbb. intros. apply andbb.
            ---
              admit.
            ---
              admit.
          -
            apply HFrame. unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb. 
            eapply HConseq.

            Focus 2.
            apply HCall with (C:= List). admit. admit. simpl. auto.
            simpl combine. simpl. apply simprefl.
            apply simprefl.
          -
            simpl. apply simprefl.
        *****
          eapply HConseq.
          -
            eapply simptrans.
            apply iffimp1. apply siffsym.
            apply FrameNotFound. apply FrameFound. reflexivity.
            apply iffimp1. apply sccom.
          -
            apply HFrame. unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb. 
            eapply HConseq with 
            (P':= (dbacc ((′ this) … repr)) <*>· 
            (( ′ xx1 ) ·=· ( ( ′ this ) … next)) </\>·
            (( ′ ft ) ·=· ( ′ xx2 )) </\>·
            b_ ( ′ xx1 ) `∈ ( ′ xx2 ) </\>·
            (b_ ( ′ xx3 ) `⊂ ( ′ xx2 ) </\>· (<!> b_ ( ′ this ) `∈ ( ′ xx3 ))) </\>·
            b_ ( ′ xx2 ) `⊂ ( ′ oldalloc ) </\>·
            (b_ ((′ this)) `∈ ((′ xx2)))
            ).
            --
              admit.
            --
              apply HFrame. unfold syn_not_dependent. simpl. solve_names. auto 100 with nsdb. 
              apply HWrite;auto. unfold pureexp. intros. admit.
            --
              apply simprefl.
          -
            unfold Imp. intros. apply impbb. intros. apply andbb.
            --
              rewrite_esem. apply andbb. apply andbb.  simpl.  unfold pnsdisj. apply PNS.is_empty_1. PNSDecide.fsetdec.
              rewrite_esem_in H1. repeat destruct_andb. handle_bops. 
              apply andbb.
              ---
                eapply veqtrans. eapply ebopmorphism. simpl. simpl in H14. apply H14. apply veqsym. simpl. simpl in H21. apply H21.
              ---
                rewrite pcall_def.
                unfold gamma, getp. simpl.
                rewrite_esem. simpl. unfold bops. autounfold with dbops. simpl. 
                case_eq (s.1.2 (↓ₚ s.1.1 this, next) `= null);intros.
                ----
                  apply notb_prop' in H8. simpl in H13.
                  assert (s.1.1 xx1 `= null).
                  eapply veqtrans. apply H13. apply H2. simpl in H8. rewrite H8 in H22. inversion H22.
                ----
                  case_eq (PS.mem (↓ₚ s.1.2 (↓ₚ s.1.1 this, next)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)));intros.
                  -----
                    case_eq (PS.subset (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) &&
                       ~~ PS.equal (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) && ~~ PS.mem (↓ₚ s.1.1 this) (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)));intros.
                    ------
                      apply andbb.
                      -------
                        admit.
                      -------
                       (*use weakning*) admit. 
                    ------
                      assert (PS.subset (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) &&
                  ~~ PS.equal (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr))  (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr)) && ~~ PS.mem (↓ₚ s.1.1 this) (↓ₛ s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr))).
                      simpl. apply andbb.
                      -------
                        admit.
                      -------
                        clear - H1 H8 H20 H10 H13.
                        simpl in H13. apply famorphism with (h1:=s.1.2) (h2:=s.1.2)  (f:= repr) in H13. Focus 2. apply veqrefl.
                        assert ((ebops `∪ (s.1.1 xx3) (euops `{}` (s.1.1 ret))) `= (s.1.2 (↓ₚ s.1.2 (↓ₚ s.1.1 this, next), repr))).
                        simpl in H1. 
                        eapply veqtrans. apply H1. eauto. 
                        apply notb_prop''.
                        apply bopmorphism with (v:=s.1.1 this) (op:=`∈) in H . autounfold with dbops in H. simpl in H. rewrite <- H.
                        apply notb_prop' in H20. simpl in H20. autounfold with dbops in H20. simpl in H20.
                        assert (↓ₚ s.1.1 this <> ↓ₚ s.1.1 ret). admit.
                        apply PS_.not_mem_iff. apply PS_.not_mem_iff in H20. PSDecide.fsetdec.
                      -------
                        rewrite H23 in H24. inversion H24.
                  -----
                    simpl in H21. apply PS.mem_2 in H15. simpl in H13. 
                    clear - H13 H15 H21 H22.
                    apply PS_.not_mem_iff in H22. 
                    assert  (PS.In (↓ₚ s.1.2 (↓ₚ s.1.1 this, next)) (↓ₛ s.1.2 (↓ₚ s.1.1 this, repr))).
                    apply veqpeq in H13. rewrite <- H13. autounfold with dbops in H21. simpl in H21. apply veqseq in H21. apply PS.equal_2 in H21. rewrite H21.
                    simpl. PSDecide.fsetdec. apply H22 in H. contradiction.
              ---
                admit.
            --
              admit.
    ++
      admit.
  +
    admit.
Admitted.