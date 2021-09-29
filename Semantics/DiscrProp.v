Require Export BaseDef.
Require Import Arith Even Div2.
Require Import Coq.Logic.Classical_Prop.

Set Implicit Arguments.


Lemma class_wretract: forall f,
  class (wretract f).
Proof.
 intros f H.
 apply (NNPP _ H).
Qed.

Lemma cover_eq_prod: forall (A B:Type) (P:A -> MF A) (Q:B -> MF B),
 (forall a, cover (eq a) (P a)) ->
 (forall b, cover (eq b) (Q b)) ->
 forall ab : A * B, 
  cover (eq ab) (fun ab' => P (fst ab) (fst ab') * Q (snd ab) (snd ab'))%U.
Proof.
 intros A B P Q HP HQ ab.
 apply cover_equiv_stable with 
  (inter (fun ab' => eq (fst ab') (fst ab)) (fun ab' => eq (snd ab') (snd ab))).
 unfold Sets.equiv, inter; split.
 intros [H1 H2].
 destruct ab; destruct x; simpl in *; rewrite H1, H2; trivial.
 intros H1.
 destruct ab; destruct x; simpl; injection H1; auto.
 apply cover_inter_mult.
 intros ab'; split; intros.
 apply (cover_eq_one _ (HP (fst ab)) (eq_sym H)).
 apply (cover_eq_zero _ (HP (fst ab)) (not_eq_sym H)).
 intros ab'; split; intros.
 apply (cover_eq_one _ (HQ (snd ab)) (eq_sym H)).
 apply (cover_eq_zero _ (HQ (snd ab)) (not_eq_sym H)).
Qed.


 Lemma even_2n : forall n, even (2*n).
 Proof.
  intro n.
  apply even_mult_l.
  repeat constructor.
 Qed.

 Lemma odd_S2n : forall n, odd (S(2*n)).
 Proof.
  intro n.
  constructor.
  apply even_2n.
 Qed.

 Lemma lub_le_n: forall (c:cpo) (f:natO -m> c) (x:c) k,
   (forall n : natO, k <= n -> f n <= x) -> 
   lub (c:=c) f <= x.
 Proof.
  intros.
  set (f' := fun n => if le_lt_dec n k then f k else f n).
  assert (Hf' : forall n : nat, f' n <= f' (S n)).
    intro; unfold f'.
    destruct (le_lt_dec (S n) k); destruct (le_lt_dec n k);
      [ trivial | exfalso; omega | apply fmon_le_compat; 
        auto with arith | apply fnatO_elim ].
  refine (@Ole_trans _ _ (lub (c:=c) (fnatO_intro Hf')) _ _ _).
    apply lub_le_compat.
    refine (ford_le_intro _); intro n; unfold f'; simpl.
    destruct (le_lt_dec n k); auto.
    apply lub_le; intros; unfold f'; simpl.
    destruct (le_lt_dec n k); auto with arith.
 Qed.

Lemma Umult_zero_left_strong: forall a b,
  (~ b == 0 -> a == 0) ->
  a * b == 0.
Proof.
 intros.
 apply (Ueq_orc b 0); [ auto | | ]; intro Hb.
   apply (Umult_zero_right_eq _ Hb).
   apply (Umult_zero_left_eq _  (H Hb)).
Qed.


(* Given two discrete disctribution over [A], restate them in terms
   of the same enumearion of [A]'s elements *)
Section SAME_ENUM.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Hypothesis is_Discr_d1 : is_Discrete d1.
 Hypothesis is_Discr_d2 : is_Discrete d2.

(* 
  parity_split f g (2m) = f m
  parity_split f g (2m+1) = g m
*)   
 Definition parity_split := fun (A:Type) (f g : nat -> A) n  =>
   match (even_odd_dec n) with
   | left x => f (div2 n)
   | right x => g (div2 (pred n)) 
   end.

 Let p1 := D_points is_Discr_d1.
 Let p2 := D_points is_Discr_d2.
 Let D1 := D_Discr is_Discr_d1.
 Let D2 := D_Discr is_Discr_d2.

 Let c1 : nat -> U := parity_split (coeff AeqU p1 d1) (fzero _).
 Let c2 : nat -> U := parity_split (fzero _) (coeff AeqU p2 d2).
 Let p  : nat -> A := parity_split p1 p2.


 Lemma disc_eqpoint_l : Discrete (@eq A) p d1.
 Proof.
  apply range_weaken with (2:=D1); fold p1.
  unfold In_classes; intros x Hx.
  unfold p, parity_split.
  unfold exc in *. 
  intros P HP H.
  apply (Hx _ HP).
  intros n Hn.
  generalize (H (2*n)%nat).
  elim (even_odd_dec (2*n)%nat); intro Hn'.
     rewrite div2_double.
     exact (fun n => n Hn).
     elimtype False; refine (not_even_and_odd _ (even_2n _) Hn').
 Qed.

 Lemma disc_eqpoint_r : Discrete (@eq A) p d2.
 Proof.
  apply range_weaken with (2:=D2); fold p2.
  unfold In_classes; intros x Hx.
  unfold p, parity_split.
  unfold exc in *. 
  intros P HP H.
  apply (Hx _ HP).
  intros n Hn.
  generalize (H (S(2*n))).
  elim (even_odd_dec (S(2*n))); intro Hn'.
     elimtype False; refine (not_even_and_odd _ Hn' (odd_S2n _)).
     rewrite <-pred_Sn, div2_double; exact (fun n => n Hn).
 Qed.

End SAME_ENUM.


Section COEFF.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d: Distr A.

 Variable p: nat -> A.
 Hypothesis H_d: Discrete (@eq A) p d.


  Variable Uleb : U -> U -> bool.
  Hypothesis Ule_eq_compat: forall x1 y1 x2 y2,
   x1 == x2->
   y1 == y2 ->
   Uleb x1 y1 = Uleb x2 y2.
  Hypothesis Uleb_corr_conv: forall x y : U, 
   x <= y -> Uleb x y.
  Hypothesis Uleb_compl_conv : forall (x y: U), 
   y < x -> Uleb x y = false.

 Lemma coeff_first_repr: forall k,
   not_first_repr AeqU p k == 0 ->
   coeff AeqU p d k == mu d (AeqU (p k)).
  Proof.
   intros k Hk.
   rewrite (mu_is_Discrete _ cover_uR (mkDiscr H_d)); simpl.
   split.
     (* left ineq *)
     rewrite <-(@serie_le _ k), (@cover_eq_one A (fun a => p k = a) _ (p k) 
         (cover_uR (p k)) (eq_refl _)); auto.
     (* right ineq *) 
     apply lub_le_n with (S k); intros n Hn.
     rewrite <-(le_plus_minus_r _ _ Hn), sigma_plus_lift, sigma_S.
     rewrite (@cover_eq_one A (fun a => p k = a) _ (p k) (cover_uR (p k)) (eq_refl _)), Umult_one_right.
     match goal with |- _ + ?X1 + ?X2 <= _ => setoid_replace X1 with (@D0 U);
       [ setoid_replace X2 with (@D0 U) | ] end; [ rewrite 2 Uplus_zero_right; trivial | | ].
     apply sigma_zero; intros n' Hn'. 
     apply (cover_elim (cover_uR (p k)) (p (S k + n'))); [ auto | | ]; intros (Heq',Heq).
       rewrite Heq; auto.
       apply Umult_zero_left_eq; apply Umult_zero_left_eq.
       rewrite (@cover_eq_one _ (fun k => exc (fun k' => (k' < k)%nat /\ p k = p k')) 
         _ (S k + n')%nat (cover_not_first_repr _ _ cover_uR p)); trivial.
       apply exc_intro with k; split; [ omega | auto ].
     apply Ule_zero_eq; rewrite <-Hk; apply sigma_le_compat; intros; auto.
  Qed.

  Lemma coeff_not_first_repr: forall k,
   not_first_repr AeqU p k == 1 ->
   coeff AeqU p d k == 0.
  Proof.
   intros k Hk.
   unfold coeff.
   rewrite Hk, Uinv_one; auto.
  Qed.

End COEFF.


Lemma exc_weaken: forall (A:Type) (P Q: A -> Prop),
  (forall a, P a -> Q a) ->
  exc P ->
  exc Q.
Proof.
 unfold exc; intros A P Q HPQ HP C H1C H2C.
 apply (HP _ H1C).
 intros a Ha; apply (H2C _ (HPQ _ Ha)).
Qed.


Section ELEM_IN_ENUM_CASE.

 Variable A:Type.
 Variable carA : A -> MF A.
 Hypothesis carA_prop: forall a, cover (fun x => a = x) (carA a).
 Variable p:nat -> A.

Lemma is_in_finite_enum: forall a n,
  orc (forall k, (k < n)%nat -> p k <> a)
      (exc (fun k => (k < n)%nat /\ p k = a /\ [1-] (sigma (fun i => carA a (p i))) k == 1)).
Proof.
 induction n.
   (* base case *)
   apply orc_left.
   intros k Hk; elim (lt_n_O _ Hk).
   (* inductive cae *)
   unfold orc in *; intros C HC H1C H2C.
   apply (IHn _ HC); clear IHn.
     (* left *)  
     intro H.
     destruct (classic (p n = a)) as [H' | H'].
       apply H2C, exc_intro with n; repeat split; trivial.
         auto with arith.
         rewrite sigma_zero; [ Usimpl; trivial | ].
         intros k Hk; apply (cover_eq_zero (p k) (carA_prop a)), 
           not_eq_sym, (H _ Hk).
       apply H1C; intros k Hk'.
       destruct (le_lt_or_eq _ _ (lt_n_Sm_le _ _ Hk')) as [Hk | Hk]; clear Hk'.
         auto.
         rewrite Hk; trivial.
     (* right *)
     intro H; apply H2C; clear H1C H2C HC C.
     unfold exc in *; intros C H1C H2C.
     apply (H _ H1C); intros k (H1k,(H2k,H3k)).
     apply H2C with k; split; [ | split ]; auto with arith.
Qed. 

Lemma is_in_enum_aux: forall k a,
  p k = a ->
  exc (fun k : nat => p k = a /\ [1-] not_first_repr carA p k == 1).
Proof.
 intros k a Hk.
 pose proof (@is_in_finite_enum (p k) (S k)) as H.
 unfold exc; unfold orc in *; intros C H1C H2C.
 apply (H _ H1C); intro H'; clear H.
   (* left *)
   elim (H' k (lt_n_Sn _) (eq_refl _)).
   (* right *)
   apply (H' _ H1C); intros k' (H1k',(H2k',H3k')).
   apply H2C with k'; split.
     rewrite <-Hk; trivial.
     unfold not_first_repr.
     rewrite H2k'; trivial.
Qed.

Lemma is_in_enum: forall (a:A), 
  orc 
   (exc (fun k => p k = a /\ [1-] not_first_repr carA p k == 1))
   (forall k, p k <> a).
Proof.
 intro a.
 apply orc_intro.
 intros H1 H2.
 apply H1; clear H1.
 destruct (Classical_Pred_Type.not_all_ex_not _ _ H2) 
   as (k', Hk'); apply NNPP in Hk'.
 apply is_in_enum_aux with k'; trivial.
Qed.

End  ELEM_IN_ENUM_CASE.


Section ENUMERATIONS_PROP.

Lemma enum_le: forall (A:Type) (d1 d2: Distr A) (p:nat -> A),
  Discrete (@eq A) p d2 ->
  d1 <= d2 ->
  Discrete (@eq A) p d1.
Proof.
 unfold Discrete, range; intros A d1 d2 p Hd2 Hd f Hf.
 split; trivial.
 rewrite (Hd f); auto.
Qed.

Lemma enum_Munit: forall (A:Type) (a:A) (p:nat -> A),
 exc (fun k : nat => a = p k) ->
 Discrete (@eq A) p (Munit a).
Proof.
 intros A a p Hp f Hf.
 refine (Hf a Hp).
Qed.

Lemma enum_Mlet: forall (A B:Type) (d: Distr A) (F:A -> Distr B) (p:nat -> A)
  (P: A -> nat -> B),
  Discrete (@eq A) p d ->
  (forall a, Discrete (@eq B) (P a) (F a)) ->
  Discrete (@eq B) (fun k => let (i, j) := bij_n_nxn k in P (p i) j) (Mlet d F).
Proof.
 intros A B d F p P Hd HF.
 red.
 apply range_Mlet with (1:=Hd).
 intros a Ha.
 apply range_weaken with (2:=HF a).
 intros b Hb.
 apply Ha;[ unfold In_classes; trivial | intros i Hi].
 apply Hb;[ unfold In_classes; trivial | intros j Hj].
 destruct (bij_surj i j) as (k, Heq).
 red; apply exc_intro with k.
 rewrite Heq.
 rewrite Hj, <- Hi; trivial.
Qed.

Lemma enum_wretract_eq: forall (A:Type) (carA : A -> MF A) (p:nat ->A),
 (forall a, cover (fun x => a = x) (carA a)) ->
 forall a, 
  wretract (fun k => [1-] not_first_repr carA p k * carA (p k) a).
Proof.
 intros A carA p carA_prop a.
 apply (@is_in_enum _ _ carA_prop p a); [ apply class_wretract | | ].
   (* case [a] is in the enumerarion [p1] *)
   intro H.
   apply H; [ apply  class_wretract | ].
   intros k' (H1k',H2k').
   assert (Haux: sigma (fun k => [1-] not_first_repr carA p k * carA (p k) a) k' == 0).
     split; trivial.
     rewrite <-Uinv_one, <-(Uinv_le_perm_right _ _ (proj2 H2k')).
     unfold not_first_repr at 2; rewrite H1k'.
     apply sigma_le_compat; intros k Hk.
     rewrite (carA_sym _ carA_prop); trivial.
   apply retract_zero_wretract with (S k').
     apply retractS_intro.
       apply retract_lt; rewrite Haux; trivial.
       rewrite Haux; Usimpl; trivial.
     intros k Hk.
     apply Umult_zero_left_strong; intro H'.
     apply (cover_elim (carA_prop (p k)) a); [ auto | | ];
       intros [H4 H5]; [ tauto | clear H' ].
     split; trivial; apply Uinv_le_perm_left; Usimpl.
     unfold not_first_repr.
     rewrite <-(sigma_incr _ Hk), sigma_S, H1k', H5; trivial.
   (* case [a] is not in the enumerarion [p1] *)
   intros H.
   apply wretract_lt; intro n; rewrite sigma_zero; trivial.
    intros k Hk.
     apply Umult_zero_right_eq.
     apply (cover_eq_zero a (carA_prop (p k)) (H _)).
 Qed.

Lemma enum_wretact_mu: forall (A:Type) (d:Distr A) (carA : A -> MF A) (p:nat ->A),
 (forall a, cover (fun x => a = x) (carA a)) ->
 wretract (fun k  => [1-] not_first_repr carA p k * mu d (carA (p k))).
Proof.
 intros A d carA p carA_prop.
 intro k.
 apply (cover_elim (cover_not_first_repr _ _ carA_prop p) k); 
    [auto | | ]; intros [H4 H5]; rewrite H5; repeat Usimpl.
     (* case [first repr k of (p k) == 1] *)
     (* Push factor [[1-] not_first_repr carA p k0] inside
       the function measured by d *)
     transitivity ([1-] (sigma (fun k => mu d 
       (fmult ([1-] not_first_repr carA p k) (carA (p k)))) k));
       [ | apply Uinv_le_compat; apply sigma_le_compat; intros; apply mu_stable_mult ].
     (* Push the [sigma] inside the function measured by d *)
     rewrite <-mu_sigma_eq.
     Focus 2.
     intros a k' Hk'; unfold fmult.
     apply (cover_elim (cover_not_first_repr _ _ carA_prop p) k'); 
     [auto | | ]; intros [_ H5'].
       (* case [first repr k' of (p k') == 1] *) 
       rewrite H5'; repeat Usimpl.
       apply (cover_elim (carA_prop (p k')) a); [auto | | ]; intros [H1 H2]. 
         rewrite H2; trivial.
         rewrite H2, sigma_zero; [auto | ].
         intros k'' Hk''.
         apply Umult_zero_right_eq.
         rewrite <-H1, (carA_sym _ carA_prop).
         apply (@sigma_zero_elim (fun i => carA (p k') (p i)) k'); trivial.
       (* case [first repr k' of (p k') == 1] *) 
       rewrite H5'; repeat Usimpl; trivial.
     (* Conclude the proof *) 
     apply mu_fplusok; intro a; unfold finv, sigma_fun, fmult.
     apply (cover_elim (carA_prop (p k)) a); [auto | | ]; intros [? Heq].
       rewrite Heq; trivial.
       rewrite Heq, sigma_zero; [auto | ].
       intros k' Hk'.
       apply Umult_zero_right_eq.
       rewrite <-H, (carA_sym _ carA_prop).
       apply (@sigma_zero_elim (fun i => carA (p k) (p i)) k); trivial.

     (* case [first repr k of (p k) == 1] *)
     trivial.
Qed.



(*
Lemma enum_Mfst: forall (A B:Type) (d: Distr (A*B)) (p:nat -> A*B),
  Discrete (@eq (A*B)) p d ->
  Discrete (@eq A) (fun k => fst (p k)) (Mfst d).
Proof.
 intros; red.
 apply range_weaken with (In_classes eq (fun k => let (i,j):=bij_n_nxn k in fst (p i))).

 unfold In_classes, exc; intros a Ha C HclassC HC.
 apply (Ha _ HclassC).
 intros k Hk.
 apply (HC (fst (bij_n_nxn k))).
 destruct (bij_n_nxn k); simpl; trivial.

 apply (enum_Mlet _ (fun ab _ => fst ab) H).
 intros (a,b); simpl.
 apply enum_Munit; refine (exc_intro _ 0%nat (eq_refl a)).
Qed.

Lemma enum_Msnd: forall (A B:Type) (d: Distr (A*B)) (p:nat -> A*B),
  Discrete (@eq (A*B)) p d ->
  Discrete (@eq B) (fun k => snd (p k)) (Msnd d).
Proof.
 intros.
 intros; red.
 apply range_weaken with (In_classes eq (fun k => let (i,j):=bij_n_nxn k in snd (p i))).

 unfold In_classes, exc; intros a Ha C HclassC HC.
 apply (Ha _ HclassC).
 intros k Hk.
 apply (HC (fst (bij_n_nxn k))).
 destruct (bij_n_nxn k); simpl; trivial.

 apply (enum_Mlet _ (fun ab _ => snd ab) H).
 intros (a,b); simpl.
 apply enum_Munit; refine (exc_intro _ 0%nat (eq_refl b)).
Qed.
*)

End ENUMERATIONS_PROP.

Add Parametric Morphism (A:Type) (p:nat -> A) : (@Discrete A (@eq A) p)
 with signature Ole (o:=Distr A) --> impl as Discrete_le_compat_morph.
Proof.
 unfold impl; eauto using enum_le.
Qed.


(* Construction of the "minimum" distribution between a pair of distributions *)
Section DISTR_MIN.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).
 Variable p: nat -> A.

(*
 Section DISTR_RESTRICTION.

  Variable d1 d2 : Distr A.
  Hypothesis H_d1: Discrete (@eq A) p d1.
  Hypothesis H_d2: Discrete (@eq A) p d2.

  Variable Uleb : U -> U -> bool.

  Hypothesis Ule_eq_compat: forall x1 y1 x2 y2,
   x1 == x2->
   y1 == y2 ->
   Uleb x1 y1 = Uleb x2 y2.
  Hypothesis Uleb_corr_conv: forall x y : U, 
   x <= y -> Uleb x y.
  Hypothesis Uleb_compl_conv : forall (x y: U), 
   y < x -> Uleb x y = false.

  Lemma restr_left_le_right: forall f,
   let P := fun a => Uleb (mu d1 (AeqU a)) (mu d2 (AeqU a)) in
   mu d1 (restr P f) <= mu d2 (restr P f).
  Proof.
  intros.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr H_d1)),
    (mu_is_Discrete _ cover_uR (mkDiscr H_d2)); simpl.
  apply serie_le_compat.
  intros k.
  apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); [auto | | ]; intros [H4 H5].
    unfold P, restr.
    rewrite (coeff_first_repr _ cover_uR H_d1 _ H5), (coeff_first_repr _ cover_uR H_d2 _ H5).
    apply (Ule_orc (mu d1 (AeqU (p k))) (mu d2 (AeqU (p k)))); [ auto | | ]; intro Hle.
      rewrite (Uleb_corr_conv _ _ Hle); auto.
      rewrite (Uleb_compl_conv Hle), 2 Umult_zero_right; auto.
    rewrite 2 (coeff_not_first_repr _ _ _ _ H5); auto.
  Qed.
 
 End DISTR_RESTRICTION.
*)

 Variable d1 d2 : Distr A.


 Hypothesis H_d1: Discrete (@eq A) p d1.
 Hypothesis H_d2: Discrete (@eq A) p d2.


 Variable Uleb : U -> U -> bool.
 Hypothesis Uleb_corr_conv: forall x y : U, 
   x <= y -> Uleb x y.
 Hypothesis Uleb_compl_conv : forall (x y: U), 
   y < x -> Uleb x y = false.

  Lemma wretract_coeff: 
    wretract (coeff AeqU p d1).
  Proof.
   unfold wretract, coeff; intros.
   apply (Ueq_orc 1 (not_first_repr AeqU p k)); [auto | | ]; intros.

  (* case [first repr k of (p k) == 0] *)
  rewrite <-H; repeat Usimpl; trivial.

  (* case [first repr k of (p k) == 1] *)
  apply (not_first_repr_bool _ cover_uR) in H.
  rewrite H; repeat Usimpl; unfold not_first_repr.
  
  (* Push factor [([1-] not_first_repr AeqU p i)] inside
     the function measured by d1 *)
  transitivity ([1-] 
   (sigma (fun i => mu d1 (fmult ([1-] not_first_repr AeqU p i) (AeqU (p i))))) k);
  [ | apply Uinv_le_compat; apply sigma_eq_compat; intros; apply mu_stable_mult].

  (* Push the [sigma] inside the function measured by d1 *)
  rewrite <-mu_sigma_eq.
  Focus 2.
  intros ? ? ?; unfold fmult.
  apply (Ueq_orc 1 (not_first_repr AeqU p k0)); [auto | | ]; intros.

  rewrite <-H1; repeat Usimpl; trivial.

  apply (not_first_repr_bool _ cover_uR) in H1.
  rewrite H1; repeat Usimpl.
  apply (cover_elim (cover_uR (p k0)) x); [auto | | ]; intros [? ?].
  rewrite H3; trivial.
  rewrite H3, sigma_zero; [auto | ].
  intros.
  assert (AeqU (p k1) x == 0).
  rewrite <-H2, (carA_sym _ cover_uR).
  apply (@sigma_zero_elim (fun i => AeqU (p k0) (p i)) k0);  trivial.
  rewrite H5; trivial.

  apply mu_fplusok; intro x; unfold finv, sigma_fun.
  apply (cover_elim (cover_uR (p k)) x); [auto | | ]; intros [? Heq].
  rewrite Heq; trivial.
  rewrite Heq, sigma_zero; [auto | ].
  intros k0 Hlt; unfold fmult.
  assert (AeqU (p k0) x == 0).
  unfold not_first_repr in H0.
  rewrite <-H0, (carA_sym _ cover_uR).
  apply (@sigma_zero_elim (fun i => AeqU (p k) (p i)) k); trivial.
  rewrite H1; trivial.

 Qed.


 Definition dmin:Distr A.
  apply PP.Discrete.
  refine (@Build_discr _ (fun k => min (coeff AeqU p d1 k) (coeff AeqU p d2 k)) _ p).
  apply wretract_le with (coeff AeqU p d1); [ auto |  apply wretract_coeff ].
 Defined.

 Lemma dmin_le_d1: forall f, mu dmin f <= mu d1 f.
 Proof.
  unfold dmin; intros; simpl.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr H_d1)); auto.
 Qed.

 Lemma dmin_le_d2: forall f, mu dmin f <= mu d2 f.
 Proof.
  unfold dmin; intros; simpl.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr H_d2)); auto.
 Qed.

 Lemma dmin_simpl: forall f, 
   let P := fun a => Uleb (mu d1 (AeqU a)) (mu d2 (AeqU a)) in
   mu dmin f == mu d1 (restr P f) + mu d2 (restr (negP P) f).
 Proof.
  intros.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr H_d1)),
     (mu_is_Discrete _ cover_uR (mkDiscr H_d2)); simpl.
  rewrite <-serie_plus; apply serie_eq_compat.
  intros k.
  apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); [auto | | ]; intros [H4 H5].

    rewrite (coeff_first_repr _ cover_uR H_d1 _ H5), (coeff_first_repr _ cover_uR H_d2 _ H5).
    apply (Ule_orc (mu d1 (AeqU (p k))) (mu d2 (AeqU (p k)))); [ auto | | ]; 
      intro Hle; unfold P, restr, negP, negb. 
      rewrite (Uleb_corr_conv _ _ Hle), (min_eq_right _ _ Hle), Umult_zero_right; auto.
      rewrite (Uleb_compl_conv Hle), (min_eq_left _ _ (Ult_le Hle)), Umult_zero_right; auto.

    rewrite 2 (coeff_not_first_repr _ _ _ _ H5).
    unfold min; repeat Usimpl; trivial.
 Qed.

End DISTR_MIN.


(* Given a distribution [d] on a product [A*B] and a distribution [d2] on [B],
   if [Msnd d <= d2], then one can compute [mu d f] as shown below *)
Section DISCR_PROJ_R.

 Variables A B: Type.

 Variable carB : B -> MF B.
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).

 Variable d2 : Distr B.
 Hypothesis Hd2_discr: is_Discrete d2.

 Variable d  : Distr (A*B).
 Hypothesis Msd_d_le_d2: forall f, 
   mu (Msnd d) f <= mu d2 f.

 Let p2 := D_points Hd2_discr.
 Let c2 := coeff carB p2 d2.

 Lemma cp_retract_p2d : forall x, 
   wretract (fun k : nat => c2 k / c2 k * carB (p2 k) x).
  Proof.
   unfold wretract; intros.
   apply (Ueq_orc 0 (c2 k)); [auto | | ]; intros.
   rewrite Udiv_by_zero; trivial; repeat Usimpl; auto.
   apply (cover_elim (carB_prop (p2 k)) x); [auto | | ]; intros [H4 H5].
   rewrite H5; repeat Usimpl; auto.
   rewrite sigma_zero; [ auto | intros].
   apply (cover_elim (carB_prop (p2 k0)) x); [auto | | ]; intros [H2 H3].
   rewrite H3; repeat Usimpl; auto.
   elim H; unfold c2, coeff.
   set (P1:=fun k => exc (fun k0 => (k0 < k)%nat /\ p2 k = p2 k0)).
   rewrite (@cover_eq_one _ P1 _ k (cover_not_first_repr (@eq B) carB carB_prop p2)).
   Usimpl; auto.
   red; apply exc_intro with k0; split; trivial.
   rewrite H2; trivial.
  Qed.


  Definition in_p2_d b := serie (fun k : nat => c2 k / c2 k * carB (p2 k) b).
  
  Lemma in_p2_d_dec : forall b, orc (in_p2_d b == 0) (in_p2_d b == 1).
  Proof.
   intros; apply orc_intro; intros.
   elim H.
   unfold in_p2_d.
   apply serie_zero.
   intros k; apply (Ueq_orc (c2 k / c2 k * carB (p2 k) b) 0); auto; intros.
   elim H0; split; trivial.
   transitivity (c2 k / c2 k * carB (p2 k) b).
   apply (Ueq_orc (c2 k)  0); auto; intros.
   elim H1; rewrite H2, Udiv_by_zero; auto.
   apply (cover_elim (carB_prop (p2 k)) b); [auto | | ]; intros [H4 H5].
   elim H1; rewrite H5; auto.
   rewrite H5, Udiv_refl; auto.
   exact (serie_le (fun k0 : nat => c2 k0 / c2 k0 * carB (p2 k0) b) k).
  Qed.

  Lemma in_p2_d_p : forall k, ~c2 k == 0 -> in_p2_d (p2 k) == 1.
  Proof.
   intros; unfold in_p2_d; split; trivial.
   transitivity (c2 k / c2 k * carB (p2 k) (p2 k)).
   rewrite Udiv_refl; [ auto | ].
   rewrite (cover_eq_one _ (carB_prop (p2 k)) (refl_equal (p2 k))).
   auto.
   auto.
   exact (serie_le (fun k0 : nat => c2 k0 / c2 k0 * carB (p2 k0) (p2 k)) k).
  Qed.


 Lemma distr_pointwise_sum_r: forall f, 
   mu d2 (fun b => mu d (fun ab => carB b (snd ab) * f ab) /
      mu d2 (carB b)) ==
   mu d f.
 Proof.
  intro f.
  rewrite (mu_is_Discrete _ carB_prop  Hd2_discr); 
    simpl; fold p2 c2.
  transitivity  (serie (fun k => mu d (fun ab => 
    (c2 k / c2 k) * (carB (p2 k) (snd ab) * f ab)))).
    apply serie_eq_compat; intros.
    rewrite <-Umult_div_assoc, Umult_sym, Umult_div_assoc, 
      Umult_sym. 
    rewrite (mu_stable_mult d (c2 k / c2 k) (fun ab => 
      carB (p2 k) (snd ab) * f ab)).
    apply Umult_eq_compat_left.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; [ unfold p2 | unfold c2 ].
      rewrite <-(coeff_first_repr _ carB_prop (D_Discr Hd2_discr) _ H5); trivial.
      rewrite (coeff_not_first_repr carB d2 _ _ H5), 2 Udiv_zero; trivial.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; [ unfold p2 | unfold c2 ].
      rewrite <-(coeff_first_repr _ carB_prop (D_Discr Hd2_discr) _ H5); trivial.
      rewrite (coeff_not_first_repr carB d2 _ _ H5); trivial.
    rewrite <-Msd_d_le_d2; simpl; apply (mu_monotonic d); intro; auto.
  rewrite <-mu_serie_eq; [ unfold serie_fun | intro x; 
    apply wretract_le with (2:=cp_retract_p2d (snd x)); auto ].
  apply (@range_eq _ (fun x => in_p2_d (snd x) == 1) d).
    intros f' Hf'; split; trivial.
    transitivity (mu d (fun p => [1-] (in_p2_d (snd p)))).
      apply (mu_monotonic d); intro x; apply (in_p2_d_dec (snd x)); 
        [auto | | ]; intros H0; [rewrite H0 | rewrite <-Hf']; auto.
    rewrite (Msd_d_le_d2 (fun b : B => [1-] in_p2_d b)),
      (mu_is_Discrete _ carB_prop  Hd2_discr); simpl; fold p2 c2.
    apply serie_zero; intros.
    apply (Ueq_orc (c2 k) 0); [auto | | ]; intros;
      [ rewrite H | rewrite in_p2_d_p; [ Usimpl | ] ]; auto.
  intros ab Hab; symmetry.
  transitivity (serie (fun k => f ab * (c2 k / c2 k * carB (p2 k) (snd ab)))); 
    [ | auto ].
  rewrite (serie_mult _ (cp_retract_p2d (snd ab))), Hab; auto.
 Qed.

End DISCR_PROJ_R.



(* Given a distribution [d] on a product [A*B] and a distribution [d1] on [A],
   if [Mfst d <= d1], then one can compute [mu d f] as shown below *)
Section DISCR_PROJ_L.

 Variables A B: Type.

 Variable carA : A -> MF A.
 Hypothesis carA_prop : forall a, cover (fun x => a = x) (carA a).

 Variable d1 : Distr A.
 Hypothesis Hd1_discr: is_Discrete d1.

 Variable d  : Distr (A*B).

 Hypothesis Msd_d_le_d2: forall f, 
   mu (Mfst d) f <= mu d1 f.

 Lemma distr_pointwise_sum_l: forall f, 
   mu d1 (fun a => mu d (fun ab => carA a (fst ab) * f ab) /
      mu d1 (carA a)) ==
   mu d f.
 Proof.
  intro f.
  set (f':=fun ba => f (swap ba)).
  transitivity (mu d1 (fun a => mu (Mswap d) (fun ba => carA a (snd ba) * f' ba) /
      mu d1 (carA a))).
    apply mu_stable_eq; refine (ford_eq_intro _); intro a.
    apply Udiv_eq_compat_left.
    unfold f', swap; simpl; apply (mu_stable_eq d); refine (ford_eq_intro _); intro ab.
      rewrite <-surjective_pairing; trivial.
  rewrite (distr_pointwise_sum_r _  carA_prop Hd1_discr (Mswap d)).
  unfold f', swap; simpl. 
  apply (mu_stable_eq d); refine (ford_eq_intro _); intro ab;
      rewrite <-surjective_pairing; trivial.
  intro g; rewrite (ford_eq_elim (Mswap_snd d) g); auto.
 Qed.

End  DISCR_PROJ_L.


(* Given a distribution on a product, if both projections  *
 * are discrete, then the distribution is discrete.        *)
Section DISCR_PRODUCT.

 Variables A B: Type.

 Variable carB : B -> MF B.
 Variable carA : A -> MF A.
 
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).
 Hypothesis carA_prop : forall a, cover (fun x => a = x) (carA a).

 Variable d  : Distr (A * B).
 
 Hypothesis discr_d1: is_Discrete (Mfst d).
 Hypothesis discr_d2: is_Discrete (Msnd d).

 Lemma discr_projs: is_Discrete d.
 Proof.
  destruct discr_d1 as [p1 H1]. 
  destruct discr_d2 as [p2 H2].
  apply mkDiscr with (fun k => (p1 (fst (bij_n_nxn k)), p2 (snd (bij_n_nxn k)))).
  unfold Discrete, range in *; simpl in *.
  intros f Hf.
  rewrite <-(distr_pointwise_sum_r _ carB_prop  discr_d2 d
    (fun _ => Ole_refl _)); simpl.
  apply H2 with (f:= fun b => 
      (mu d) (fun ab : A * B => carB b (snd ab) * f ab) /
      (mu d) (fun ab : A * B => carB b (snd ab))).

  intros b Hb; apply Hb; [ auto | intros kb Hkb ].
  symmetry; apply Udiv_zero_eq.
  rewrite <-(distr_pointwise_sum_l _ carA_prop  discr_d1 d
    (fun _ => Ole_refl _)); simpl.
  apply H1 with (f:= fun a  => mu d
    (fun ab => carA a (fst ab) * (carB b (snd ab) * f ab)) /
    mu d (fun ab => carA a (fst ab))).
  intros a Ha; apply Ha; [ auto | intros ka Hka ].
  symmetry; apply Udiv_zero_eq.

  rewrite <-(mu_zero d); unfold fzero;
  apply mu_stable_eq; refine (ford_eq_intro _).
  intros (a',b'); simpl.
  apply (cover_elim (carB_prop b) b'); [ auto | | ]; intros [H4 H5].
    rewrite H5; repeat Usimpl; trivial.
    rewrite H5, <-H4; Usimpl; clear H4 H5.
    apply (cover_elim (carA_prop a) a'); [ auto | | ]; intros [H4 H5].
      rewrite H5; repeat Usimpl; trivial.
      rewrite H5, <-H4; Usimpl; clear H4 H5.
      apply Hf.
      destruct (bij_surj ka kb) as [k Hk].
      apply exc_intro with k.
      rewrite Hk; simpl; rewrite Hkb, Hka; trivial.
 Qed.

End DISCR_PRODUCT.


 Lemma discr_ext: forall (A:Type) (d1 d2: Distr A),
   (forall f, mu d1 f == 0 -> mu d2 f == 0) ->
   is_Discrete d1 ->
   is_Discrete d2.
 Proof.
  intros A d1 d2 Hd [p Hdis1].
  apply mkDiscr with p.
  unfold Discrete in *.
  intros f Hf.
  symmetry; apply Hd. 
  symmetry; apply (Hdis1 _ Hf).
 Qed.


 Lemma Discr_distr_comm_elim: forall (A B:Type) (carA : A -> MF A) 
   (d1: Distr A) (d2:Distr B), 
   (forall a : A, cover (eq a) (carA a)) ->
   is_Discrete d1 ->
   forall f,
   mu d1 (fun a => mu d2 (fun b => f a b)) ==
   mu d2 (fun b => mu d1 (fun a => f a b)).
 Proof.
  intros.
  generalize (eq_distr_elim  (is_Discrete_commute _ H X d2) 
    (fun ab => f (snd ab) (fst ab))).
  unfold prod_distr; auto.
 Qed.


Section RANGE_CHARACT.

 Variables A: Type.
 Variable d  : Distr A.
 Variable R : A -> Prop.
 
 Hypothesis discr_d1: is_Discrete d.

 Variable carA : A -> MF A.

 Hypothesis carA_prop : forall a, cover (fun x => a = x) (carA a).

 Lemma carA_sym: forall a1 a2, carA a1 a2 == carA a2 a1.
 Proof.
   intros.
   apply (cover_elim (carA_prop a1) a2); [ auto | | ]; intros (H,H').
     rewrite H', (@cover_eq_zero _ _ _ a1 (carA_prop a2)); auto.
     rewrite H', (@cover_eq_one _ _ _ a1 (carA_prop a2)); auto.
 Qed.

     
 Lemma range_discr_elim: 
   range R d -> 
   forall (a:A), ~ 0 == mu d (carA a) -> R a.
 Proof.
   intros Hran a Ha.
   apply NNPP; intro H; apply Ha; clear Ha.
   apply Hran; intros a' Ha'.
   rewrite carA_sym; symmetry; 
     apply (@cover_eq_zero _ _ _ a (carA_prop a')).
   intros H'; subst; tauto.
 Qed.

 Lemma range_discr_intro: 
  (forall (a:A), ~ 0 == mu d (carA a) -> R a) ->
  range R d.
 Proof.
  intros H f Hf.
  rewrite (mu_is_Discrete _ carA_prop discr_d1); simpl.
  symmetry; apply serie_zero; intros.
  apply (Ueq_orc (coeff carA (D_points discr_d1) d k) 0); [ auto | | ]; intro Hk.
    rewrite Hk; auto.
    destruct discr_d1 as (p, Hdiscr); simpl in *.
    apply (cover_elim (cover_not_first_repr _ _ carA_prop p) k); 
      [auto | | ]; intros [_ Hpk].
      (* case first repr *)
      rewrite (coeff_first_repr _ carA_prop Hdiscr _ Hpk).
      apply Umult_zero_right_eq. 
      symmetry; apply Hf; apply H.
      intro H'; elim Hk; apply Ule_zero_eq; rewrite H'.
      rewrite (mu_is_Discrete _ carA_prop (mkDiscr Hdiscr)); simpl.
      rewrite <-(serie_le _ k), (@cover_eq_one A (fun a => p k = a) _ (p k) 
        (carA_prop (p k)) (eq_refl _)); auto.
      (* case not first repr *)
      rewrite (coeff_not_first_repr _ _ _ _ Hpk); auto.
 Qed.

End RANGE_CHARACT. 


Section RANGE_STRENGTHEN.

 Variables A: Type.
 Variable d  : Distr A.
 Variable R S: A -> Prop.

 Hypothesis discr_d1: is_Discrete d.

 Variable carA : A -> MF A.
 Hypothesis carA_prop : forall a, cover (fun x => a = x) (carA a).

 Lemma range_discr_strengthen: 
   range R d ->
   range S d ->
   range (fun a => R a /\ S a) d.
 Proof.
  intros HR HS.
  apply (range_discr_intro _ discr_d1 _ carA_prop). 
  intros a Ha; split.
    apply (range_discr_elim _ carA_prop HR _ Ha).
    apply (range_discr_elim _ carA_prop HS _ Ha).
 Qed.

End RANGE_STRENGTHEN.


Section SERIE_OVER_PRODUCT_SPLIT_L.

 Variables A B: Type.
 Variable carA : A -> MF A.
 Variable carB : B -> MF B.

 Variable p:nat -> (A*B).

 Hypothesis carA_prop : forall b, cover (fun x => b = x) (carA b).
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).

 Definition carProd: A*B -> MF (A*B) :=
   fun ab => fun ab' => carA (fst ab) (fst ab') * carB (snd ab) (snd ab').

 Lemma  carProd_prop: forall ab, cover (fun x => ab = x) (carProd ab). 
 Proof.
  apply (cover_eq_prod _ _ carA_prop carB_prop).
 Qed.

 Lemma sigma_prod_split_l: forall H,
  serie (fun k =>  [1-] not_first_repr carProd p k * H (p k)) ==
  serie (fun kb => [1-] not_first_repr carB (fun k => snd (p k)) kb *
     serie (fun ka =>  [1-] not_first_repr carProd p ka * carB (snd (p ka)) (snd (p kb)) *
       H (fst (p ka), snd (p kb)))).
 Proof.
  generalize carA_prop, carB_prop.
  admit.
 Qed.

End SERIE_OVER_PRODUCT_SPLIT_L.

Section SERIE_OVER_PRODUCT_SPLIT_R.

 Variables A B: Type.
 Variable carA : A -> MF A.
 Variable carB : B -> MF B.

 Variable p:nat -> (A*B).

 Hypothesis carA_prop : forall b, cover (fun x => b = x) (carA b).
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).

 Lemma sigma_prod_split_r: forall H,
  serie (fun k =>  [1-] not_first_repr (carProd carA carB) p k * H (p k)) ==
  serie (fun ka => [1-] not_first_repr carA (fun k => fst (p k)) ka *
     serie (fun kb =>  [1-] not_first_repr (carProd carA carB) p kb * carA (fst (p kb)) (fst (p ka)) *
       H (fst (p ka), snd (p kb)))).
 Proof.
  intro H.
  set (H':= fun ba => H (swap ba)).
  set (p':= fun k => swap (p k)). 
  transitivity (serie (fun k => [1-] not_first_repr (carProd carB carA) p' k * H' (p' k))). 
    apply serie_eq_compat; intro k; apply Umult_eq_compat.
      Usimpl; unfold not_first_repr.
      apply sigma_eq_compat; intros k' Hk'; unfold carProd, p'; simpl; auto.
      unfold H', p', swap; simpl; rewrite <-surjective_pairing; trivial.
  rewrite (sigma_prod_split_l _ _ _ carB_prop carA_prop).
    apply serie_eq_compat; intro ka; apply Umult_eq_compat.
      Usimpl; unfold not_first_repr.
      apply sigma_eq_compat; intros k' Hk'; unfold p'; simpl; auto.
      apply serie_eq_compat; intro kb; repeat apply Umult_eq_compat.
        Usimpl; unfold not_first_repr; apply sigma_eq_compat; 
          intros k' Hk'; unfold carProd, p'; simpl; auto.
        unfold p'; simpl; trivial.
        unfold H', p', swap; simpl; trivial.
 Qed.

End SERIE_OVER_PRODUCT_SPLIT_R.











(*
Section DISCR_PROJ'.

 Variables B: Type.

 Variable carB : B -> MF B.
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).

 Variable d2 : Distr B.
 Hypothesis Hd2_discr: is_Discrete d2.

 Variable d  : Distr B.

 Let p2 := D_points Hd2_discr.
 Let c2 := coeff carB p2 d2.


 Hypothesis d_le_d2: forall f, 
   mu d f <= mu d2 f.


 Lemma distr_pointwise_sum': forall f, 
   mu d2 (fun b => mu d (fun b' => carB b b' * f b') /
      mu d2 (carB b)) ==
   mu d f.
 Proof.
  intro f.
  rewrite (mu_is_Discrete _ carB_prop  Hd2_discr); 
    simpl; fold p2 c2.
  transitivity  (serie (fun k => mu d (fun b' => 
    (c2 k / c2 k) * (carB (p2 k) b' * f b')))).
    apply serie_eq_compat; intros.
    rewrite <-Umult_div_assoc, Umult_sym, Umult_div_assoc, 
      Umult_sym. 
    rewrite (mu_stable_mult d (c2 k / c2 k) (fun b' => 
      carB (p2 k) b' * f b')).
    apply Umult_eq_compat_left.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; [ unfold p2 | unfold c2 ].
      rewrite <-(coeff_first_repr _ carB_prop (D_Discr Hd2_discr) _ H5); trivial.
      rewrite (coeff_not_first_repr carB d2 _ _ H5), 2 Udiv_zero; trivial.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; [ unfold p2 | unfold c2 ].
      rewrite <-(coeff_first_repr _ carB_prop (D_Discr Hd2_discr) _ H5); trivial.
      rewrite (coeff_not_first_repr carB d2 _ _ H5); trivial.
    rewrite <-d_le_d2; simpl; apply (mu_monotonic d); intro; auto.
  rewrite <-mu_serie_eq; [ unfold serie_fun | intro x; apply wretract_le 
    with (2:=cp_retract_p2d _ carB_prop Hd2_discr x); auto ].
  apply (@range_eq _ (fun x => in_p2_d carB Hd2_discr x == 1) d).
    intros f' Hf'; split; trivial.
    transitivity (mu d (fun p => [1-] (in_p2_d carB Hd2_discr p))).
      apply (mu_monotonic d); intro x; apply (in_p2_d_dec _ carB_prop Hd2_discr x); 
        [auto | | ]; intros H0; [rewrite H0 | rewrite <-Hf']; auto.
    rewrite (d_le_d2 (fun b : B => [1-] in_p2_d carB Hd2_discr b)),
      (mu_is_Discrete _ carB_prop  Hd2_discr); simpl; fold p2 c2.
    apply serie_zero; intros.
    apply (Ueq_orc (c2 k) 0); [auto | | ]; intros;
     [ rewrite H | unfold p2; rewrite (in_p2_d_p carB_prop Hd2_discr); 
       [ Usimpl | ] ]; auto.
  intros b Hb; symmetry.
  transitivity (serie (fun k => f b * (c2 k / c2 k * carB (p2 k) b))); 
    [ | auto ].
  unfold c2, p2; rewrite (serie_mult _ (cp_retract_p2d _ carB_prop Hd2_discr b)). 
  unfold in_p2_d in Hb; rewrite Hb; auto.
 Qed.


 Hypothesis d2_le_d: forall f, 
   mu d2 f <= mu d f.

 Lemma distr_pointwise_sum'': forall f, 
   mu d2 (fun b => mu d (fun b' => carB b b' * f b') /
     mu d (carB b)) ==  mu d2 f.
 Proof.
  intro f.
  rewrite 2 (mu_is_Discrete _ carB_prop  Hd2_discr); 
    simpl; fold p2 c2.
  apply serie_eq_compat; intro k.
  transitivity (c2 k * f (p2 k) * (mu d (carB (p2 k)) / mu d (carB (p2 k)))).
    rewrite <-Umult_assoc; Usimpl.
    rewrite <-(Umult_div_assoc _ _ _ (Ole_refl _)); apply Udiv_eq_compat_left.
    rewrite <-(mu_stable_mult d (f (p2 k))).
    apply (mu_stable_eq d); unfold fmult; refine (ford_eq_intro _); intro b; 
      rewrite Umult_sym.
    apply (cover_elim (carB_prop (p2 k)) b); [ auto | | ]; 
        intros [H4 H5]; rewrite H5; repeat Usimpl; [ | rewrite H4 ]; trivial.
  apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k);
    [auto | | ]; intros [_ H5]. 
    unfold c2, p2; rewrite (coeff_first_repr _ carB_prop (D_Discr Hd2_discr) _ H5);
      fold p2 c2; clear H5.
    apply (Ueq_orc 0 (mu d (carB (p2 k)))); [ auto | | ]; intro H6.
      rewrite (Udiv_zero_eq _ H6); Usimpl; symmetry; apply Umult_zero_left_eq; 
        apply Ule_zero_eq; rewrite H6; apply d2_le_d.
      rewrite (Udiv_refl H6); auto.
    unfold c2; rewrite (coeff_not_first_repr carB d2 _ _ H5); repeat Usimpl; trivial.
 Qed.

End DISCR_PROJ'.
*)

(*
Section DISCR_PROJ_LE.

 Variables A B: Type.

 Variable carB : B -> MF B.
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).

 Variable d2 : Distr B.
 Hypothesis Hd2_discr: is_Discrete d2.

 Variable d  : Distr (A*B).

 Let p2 := D_points Hd2_discr.
 Let c2 := coeff carB p2 d2.

 Variable F : B -o> U.
 Variable ep: U.

 Hypothesis Fbound1: forall k,
   not_first_repr carB p2 k == 0 ->
   F (p2 k) <= mu d2 (carB (p2 k)) * ep.

 Hypothesis Fbound2: forall k,
   not_first_repr carB p2 k == 1 ->
   F (p2 k) == 0.

 Lemma distr_pointwise_le: 
   mu d2 (fun b => F b /
      mu d2 (carB b)) <= ep.
 Proof.
  rewrite (mu_is_Discrete _ carB_prop  Hd2_discr); 
    simpl; fold p2 c2.
  transitivity  (serie (fun k => F (p2 k))).
    apply serie_le_compat; intro k.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; [ unfold p2 | unfold c2 ].
      rewrite <-(coeff_first_repr _ carB_prop (D_Discr Hd2_discr) _ H5); 
        fold p2 c2; apply Umult_div_le.
      rewrite (coeff_not_first_repr carB d2 _ _ H5); Usimpl; auto.
  rewrite <-(mu_cte_le d2 ep).
  rewrite (mu_is_Discrete _ carB_prop  Hd2_discr); 
    simpl; fold p2 c2.
  unfold fcte.
  apply serie_le_compat.
  intro k.
  apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5].
    unfold c2, coeff; rewrite H5; repeat Usimpl; auto.
    unfold c2, coeff; rewrite H5; repeat Usimpl; auto.
 Qed.

End DISCR_PROJ_LE.
*)    

