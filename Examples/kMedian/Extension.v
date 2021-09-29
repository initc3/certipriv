Require Import BoolEquality.
Require Import BaseDef.
Require Import MSets.
Require Import Reals.
Require Import Fourier.
Require Import CCMisc.
Require Import le_lift.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.

(* *********************************************************************** *)
(*                           1.Some auxiliary lemmas                       *)
(* *********************************************************************** *)

Lemma R_dist_le : forall x y l,
 0 <= x <= l ->
 0 <= y <= l ->
 R_dist x y <= l.
Proof.
 intros x y l (H1x, H2x) (H1y, H2y).
 unfold R_dist, Rabs.
 destruct (Rcase_abs (x - y)); fourier.
Qed.

Lemma prod_dec:  forall (A B : Type),
  (forall (a1 a2:A), {a1 = a2} + {~ a1 = a2}) ->
  (forall (b1 b2:B), {b1 = b2} + {~ b1 = b2}) ->
  forall (ab1 ab2: A*B), { ab1 = ab2} + {~ ab1 = ab2}.
Proof.
 intros A B HA HB (a1,b1) (a2,b2).
 destruct (HA a1 a2).
   destruct (HB b1 b2).
     subst; left; trivial.
     right; intros H; inversion H; tauto.
   right; intros H; inversion H; tauto.
Qed.

Lemma NoDupA_NoDup: forall (A:Type) (l:list A), 
  NoDupA eq l -> NoDup l.
Proof.
 intros; induction l.
   trivial.
   inversion H; subst.
   constructor.
   intro H'; apply (H2 (In_InA eq_equivalence H')).
   auto.
Qed.
    
Lemma InA_In: forall (A:Type) (a:A) (l:list A), 
  InA eq a l <-> List.In a l. 
Proof.
 split; intros.
   induction l.
     rewrite InA_nil in H; elim H.
     inversion H; subst; [ apply in_eq |
       apply (in_cons _ _ _ (IHl H1)) ].
   apply (In_InA eq_equivalence H).
Qed.

Lemma Permutation_PermutP: forall (A:Type) (l1 l2:list A), 
  Permutation l1 l2 -> PermutP eq l1 l2.
Proof.
 intros.
 induction H.
   constructor.
   apply PermutP_cons; trivial.
   apply permP_swap with (x:=y) (l:=x::l) (l1':=x::List.nil) 
       (x':=y) (l2':=l); [ trivial | ].
   apply (PermutP_cons _ _ (eq_refl _)), PermutP_refl; intros; trivial.
   apply PermutP_trans with l'; trivial.
Qed.

Lemma fold_right_Perm: forall (A:Type) (a:A) (f: A -> A -> A),
  (forall x y z, f x (f y z) = f y (f x z)) ->
  forall (l1 l2: list A), 
    PermutP (@eq _) l1 l2 ->
    fold_right f a l1 = fold_right f a l2.
Proof.
 intros A a f Hf.
 induction 1.
   trivial.
   subst; simpl; clear H0.
   rewrite IHPermutP. 
   clear IHPermutP; induction l1'.
     trivial.
     change (f x' (f a0 (fold_right f a (l1' ++ l2'))) =
       f a0 (fold_right f a (l1' ++ x' :: l2'))).
     rewrite <-IHl1'; trivial.
Qed.





(* *********************************************************************** *)
(*                   2.[Discretize] for a finite domain.                   *)  
(* *********************************************************************** *)

Section Finite_Discretize.

 Variable A B:Type.
 
 Variable s: A -> B -> R.

 Variable Out : list B.
 Hypothesis Out_spec:
  {b:B | List.In b Out /\ forall a, s a b > 0} + {Out = @List.nil B}.

 Hypothesis s_pos: forall a b, 0 <= s a b .

 Variable dummy:B.

 (* For each [a in A], pick an element [b in Out] with 
    probability proportional to [s a b] *)
 Definition finite_discr: A -> Distr (B). 
  intro a.
  destruct Out_spec as [ (b,(H1b,H2b)) | HOut ].
    refine (@finite_distr _ Out (fun b => s a b) (s_pos a) b H1b (H2b a)).
    exact (Munit dummy).
 Defined.

 Lemma finite_discr_is_Discrete: forall a,
   is_Discrete (finite_discr a).
 Proof.
  intros a; unfold finite_discr.
  destruct Out_spec as [ (b,(H1b,H2b)) | HOut ].
    apply finite_distr_discrete.
    apply is_Discrete_Munit.
 Qed.

 Lemma finite_discr_lossless: forall a,
   mu (finite_discr a) (fun _ => 1)%U == 1%U.
 Proof.
  intros; unfold finite_discr.
  destruct Out_spec as [ (b,(H1b,H2b)) | HOut ].
    apply finite_distr_lossless.
    trivial.
 Qed.

 Variable eqU: B -> B -O-> U.
 Hypothesis eqU_spec: forall b:B, cover (eq b) (eqU b).

 Hypothesis Hdec: forall (b:B), {List.In b Out} + {~ List.In b Out}.
 Hypothesis Out_NoDup: NoDup Out.


 Section Assym_Distance.

  Variables a a':A.
  Variables M M':R.
  Hypothesis HM:  forall b, List.In b Out -> s a b  <= M  * s a' b.
  Hypothesis HM': forall b, List.In b Out -> s a' b <= M' * s a  b.
  Hypothesis HM_pos:  0 <= M.  
  Hypothesis HM'_pos: 0 <= M'.  

  Lemma finite_discr_assym_dist: 
   let d1 := finite_discr a in 
   let d2 := finite_discr a' in 
   let lam := M * M' in 
   1 <= lam -> 
   forall (b:B), (mu d1 (eqU b) <= lam ** mu d2 (eqU b))%tord.
  Proof.
   intros d1 d2 lam Hlam b.
   unfold d1, d2, finite_discr.
   destruct Out_spec as [ (b',(H1b',H2b')) | HOut ].
   (* case [Out] not empty *)
   destruct (Hdec b) as [Hb | Hb].
     (* case [ b in Out ] *)
     rewrite 2 finite_distr_in; trivial. 
     unfold multRU; repeat case_Rle; trivial; [ | elim n; 
       apply Rmult_le_pos; [ apply Rmult_le_pos; trivial | apply iR_ge_0 ] ].
     assert (Haux: forall x, 0 < y Out (fun b0 : B => s x b0)) by
       (intro x; refine (y_gt_0 _ _ (s_pos x) _ H1b' (H2b' x))). 
     unfold c; rewrite retract_R.
     Focus 2.
     split; [ apply Rdiv_pos; trivial | ].
     apply Rdiv_le_1; trivial.
     unfold y; generalize Out b Hb; clear -s_pos.
     induction Out; intros.
       elim (in_nil Hb).
       simpl; destruct (in_inv Hb).
         subst; apply Rle_plus_l.
         clear -s_pos; induction l; simpl; 
           [ trivial | rewrite <-s_pos, <-IHl; fourier ].
         rewrite (IHl _ H); apply (Rle_plus_r _ (s_pos _ _)).
     apply iU_le_morphism; unfold lam.
     generalize (Haux a) (Haux a');
     set (y1:= y Out (fun b0 : B => s a b0));
     set (y2:= y Out (fun b0 : B => s a' b0));
     clear -s_pos HM HM' HM_pos HM'_pos Hb; intros Hy1 Hy2.
     transitivity (M * (s a' b / y1)).
     replace (M * (s a' b / y1)) with ((M * s a' b) / y1) by
       (field; intro; fourier); apply Rdiv_le_compat; auto.
     rewrite Rmult_assoc; apply Rmult_le_compat_l; trivial.
     replace (M' * (s a' b / y2)) with (s a' b * (M' / y2)) by 
       (field; intro; fourier); apply Rmult_le_compat_l; trivial.
     apply Rmult_le_reg_r with y2; [trivial | rewrite (Rdiv_mult _ Hy2) ].
     apply Rmult_le_reg_r with y1; [trivial | ];
     replace (/ y1 * y2 * y1) with y2  by (field; intro; fourier).
     unfold y2, y1, y.
     rewrite <-fold_right_Rplus_mult.
     apply fold_right_Rplus_monotonic; auto.
     (* case [b not_in Out] *)
     rewrite 2 finite_distr_notin; trivial.  
   (* case [Out] empty *)
   simpl; rewrite <-(multRU_1_l (eqU b dummy)) at 1; 
     apply multRU_le_compat; trivial; fourier.
  Qed.
 
 End Assym_Distance.


 Section Symm_Distance.

  Variables a a':A.
  Variables M:R.
  Hypothesis HM1: forall b, List.In b Out -> s a  b <= M * s a' b.
  Hypothesis HM2: forall b, List.In b Out -> s a' b <= M * s a  b.
  Hypothesis HM_pos:  0 <= M.  

  Lemma finite_discr_symm_dist: 
   let d1 := finite_discr a in 
   let d2 := finite_discr a' in 
   let lam := M * M in 
   (1 <= M) ->
   le_dist d1 d2 lam D0.
  Proof.
   intros.
   assert (d1_discr: is_Discrete d1) by apply finite_discr_is_Discrete.
   assert (d2_discr: is_Discrete d2) by apply finite_discr_is_Discrete.
   set (p:=parity_split (D_points d1_discr) (D_points d2_discr)).
   refine (le_dist_discr_serie_intro _ eqU_spec _ 
     (disc_eqpoint_l d1_discr d2_discr) (disc_eqpoint_r d1_discr d2_discr) _ _ _).
     rewrite <-(Rmult_1_r 1); apply Rmult_le_compat; trivial; fourier.
   apply serie_zero; intro k. 
   split; trivial; apply Uminus_le_zero.
   apply (cover_elim (cover_not_first_repr _ _  eqU_spec p) k); 
     [auto | | ]; intros [H4 H5].
     rewrite (coeff_first_repr _ eqU_spec (disc_eqpoint_l d1_discr d2_discr) _ H5),
       (coeff_first_repr _ eqU_spec (disc_eqpoint_r d1_discr d2_discr) _ H5); fold p.
     apply finite_discr_assym_dist; trivial.
     rewrite <-(Rmult_1_r 1); apply Rmult_le_compat; trivial; fourier.
     fold p; rewrite (coeff_not_first_repr _ _ _ _ H5); trivial.
   apply serie_zero; intro k. 
   split; trivial; apply Uminus_le_zero.
   apply (cover_elim (cover_not_first_repr _ _  eqU_spec p) k); 
     [auto | | ]; intros [H4 H5].
     rewrite (coeff_first_repr _ eqU_spec (disc_eqpoint_l d1_discr d2_discr) _ H5),
       (coeff_first_repr _ eqU_spec (disc_eqpoint_r d1_discr d2_discr) _ H5); fold p.
     apply finite_discr_assym_dist; trivial.
     rewrite <-(Rmult_1_r 1); apply Rmult_le_compat; trivial; fourier.
     fold p; rewrite (coeff_not_first_repr _ _ _ _ H5); trivial.
  Qed.  

 End Symm_Distance.

End Finite_Discretize.


(* Exponential distribution over a finite carrier set, 
   antimonotonic wrt the scoring function -ie the higher 
   the score function, the less likely- *)
Section Finite_Exp_Antimonot.

 Variable A B:Type.

 Variable eps : R.
 Hypothesis eps_pos : 0 <= eps.

 Variable f: A -> B -> R.

 Let s := fun a b => exp (- eps * f a b).

 Variable Out : list B.
 Hypothesis Out_spec:
  {b:B | List.In b Out} + {Out = @List.nil B}.

 Let s_pos: forall a b, 0 <= s a b.
 Proof.
  intros; unfold s; left; apply exp_pos.
 Qed.

 Variable dummy:B.  

 Definition exp_antimon: A -> Distr (B). 
  intro a. 
  refine (@finite_discr _ _ s Out _ s_pos dummy a).
  destruct Out_spec as [ (b,Hb) | HOut ].
    left; exists b; split; [ trivial | intros; apply exp_pos ].
    right; subst; trivial.
 Defined.

 Lemma exp_antimon_is_Discr: forall a,
   is_Discrete (exp_antimon a).
 Proof.
  intro a; apply (finite_discr_is_Discrete _ _ dummy).
 Qed.

 Lemma exp_antimon_lossless:  forall a,
   mu (exp_antimon a) (fun _ => 1%U) == 1%U.
 Proof.
  intros; apply finite_discr_lossless.
 Qed.

 Variable eqU: B -> B -O-> U.
 Hypothesis eqU_spec: forall b:B, cover (eq b) (eqU b).

 Hypothesis Hdec: forall (b:B), {List.In b Out} + {~ List.In b Out}.
 Hypothesis Out_NoDup: NoDup Out.

 Variables a a':A.
 Variables M:R.
 Hypothesis HM: forall b, List.In b Out -> R_dist (f a b) (f a' b) <= M.
 Hypothesis M_pos: 0 <= M.

 Lemma exp_antimon_dist:
  let d1 := exp_antimon a in 
  let d2 := exp_antimon a' in 
  let lam := exp (2 * eps * M) in
  le_dist d1 d2 lam D0.
 Proof.
  intros.
  apply le_dist_weaken_lam with (exp (eps * M) * exp (eps * M)).
    split; [ left; apply Rmult_lt_0_compat; apply exp_pos |
      unfold lam; rewrite Rmult_assoc, double, exp_plus; trivial ].
  refine (@finite_discr_symm_dist _ _ s Out _ s_pos dummy _ eqU_spec 
    Hdec Out_NoDup _ _ _ _ _ _ _).
    intros b Hb; unfold s.
    rewrite <-exp_plus; apply exp_monotonic.
    replace (eps * M + - eps * f a' b) with (eps * (M - f a' b)) by ring.
    replace (- eps * f a b) with (eps * (- f a b)) by ring.
    refine (Rmult_le_compat_l _ _ _ eps_pos _); apply Rplus_le_perm_right.
    rewrite Rplus_comm, <-(HM Hb), R_dist_sym; apply Rle_abs.
    intros b Hb; unfold s.
    rewrite <-exp_plus; apply exp_monotonic.
    replace (eps * M + - eps * f a b) with (eps * (M - f a b)) by ring.
    replace (- eps * f a' b) with (eps * (- f a' b)) by ring.
    refine (Rmult_le_compat_l _ _ _ eps_pos _); apply Rplus_le_perm_right.
    rewrite Rplus_comm, <-(HM Hb); apply Rle_abs.
    left; apply exp_pos.
    rewrite <-exp_0 at 1; apply exp_monotonic; apply Rmult_le_pos; trivial. 
 Qed.

End Finite_Exp_Antimonot.




(* *********************************************************************** *)
(*         3.Two exponential distributions over a quasimetric space        *)
(* *********************************************************************** *)

(* Finite set equipped with a quasi-metric
   --ie we do not require symmetry-- *)
Module Type FiniteQuasiMetricSpace.

 Declare Module E : UsualDecidableType.
 Declare Module Set_of_E : WSetsOn E.

 (* QuasiMetric specification *)
 Parameter Delta : E.t -> E.t -> R.
 Hypothesis Delta_pos: forall (x1 x2:E.t), 0 <= Delta x1 x2.
 Hypothesis Delta_triang: forall (x1 x2 x3:E.t),
   Delta x1 x3  <= Delta x1 x2 + Delta x2 x3.
 Hypothesis Delta_eq: forall (x:E.t), Delta x x = 0.

 (* Diameter of the QuasiMetric *)
 Parameter Diameter : R.
 Hypothesis Diam_spec: forall (x1 x2:E.t), 
   Delta x1 x2 <= Diameter.

 (* Distance between a point [x] and a set of points [F] *)
 Definition DeltaSet (x:E.t) (F:Set_of_E.t) := 
   Set_of_E.fold (fun p r => Rmin r (Delta p x)) F Diameter.

 Lemma DeltaSet_Bound: forall d F,
   0 <= DeltaSet d F <= Diameter.
 Proof.
  intros.
  unfold DeltaSet; rewrite Set_of_E.fold_spec; unfold Basics.flip.
  rewrite <-fold_left_rev_right.
  induction (rev (Set_of_E.elements F)).
    simpl; split.
    rewrite <-(Delta_eq d); apply Diam_spec.
    trivial.
    destruct IHl; simpl; split.
      apply Rmin_glb; [trivial | apply Delta_pos].
      rewrite Rmin_r; apply Diam_spec.
 Qed.

 
 Parameter compl: Set_of_E.t -> Set_of_E.t.
 Hypothesis compl_spec : forall (p:E.t) (X:Set_of_E.t),
   Set_of_E.In p (compl X) <-> ~  Set_of_E.In p X.

 Parameter Set_of_E_eqb:  Set_of_E.t -> Set_of_E.t -> bool.
 Hypothesis Set_of_E_eqb_spec: forall X1 X2, 
   if  Set_of_E_eqb X1 X2 then X1 = X2 else X1 <> X2.


End FiniteQuasiMetricSpace.


(* Extension of a quasimetric with a notion of 
   distance from a set wrt another, and definition
   of two distributions on top of this notion *)
Module QMetricExtension (M: FiniteQuasiMetricSpace).

 Export M.

 (* Distance of [D] wrt [F] *)
 Definition cost (F D: Set_of_E.t) := 
   fold_right Rplus 0 (map (fun p => DeltaSet p F) (Set_of_E.elements D)). 

 (* Sets adjacency *)
 Definition adj_sets (X Y:Set_of_E.t) := 
   exists Z, exists x, exists y,
   X = (Set_of_E.add x Z) /\ Y = (Set_of_E.add y Z) 
   /\ ~ Set_of_E.mem x Z /\  ~ Set_of_E.mem y Z.

 (* Sensitivity of the [cost] function *) 
 Lemma cost_sensitivity: forall (F D1 D2: Set_of_E.t),
   adj_sets D1 D2 -> 
   R_dist (cost F D1) (cost F D2) <= Diameter. 
 Proof.
   intros F D1 D2 (D,(d1,(d2,(?,(?,(H1,H2)))))); subst; unfold cost.
   match goal with
   |- R_dist (fold_right Rplus 0 ?l1') (fold_right Rplus 0 ?l2') <= _ => 
     rewrite fold_right_Perm with (l1:=l1') 
       (l2:=map (fun p : E.t => DeltaSet p F) (d1 :: Set_of_E.elements D)); [ 
     rewrite fold_right_Perm with (l1:=l2') 
       (l2:=map (fun p : E.t => DeltaSet p F) (d2 :: Set_of_E.elements D)) | | ]
   end.
   simpl; rewrite R_dist_plus, R_dist_eq, Rplus_0_r.
   apply R_dist_le; apply DeltaSet_Bound.
   intros; ring.
   apply PermutP_map, PermutP_sym, PermutP_map.
   apply PermutP_weaken with eq; [ intros; subst; trivial | ].
   apply Permutation_PermutP, NoDup_Permutation.
     apply NoDup_cons.
       unfold is_true in H2; rewrite Set_of_E.mem_spec, <-Set_of_E.elements_spec1 in H2;
       intro H; apply H2; apply (In_InA E.eq_equiv H).
       apply (NoDupA_NoDup (Set_of_E.elements_spec2w _)).
     apply (NoDupA_NoDup (Set_of_E.elements_spec2w _)).
     intros; rewrite <- 2 InA_In.
     rewrite InA_cons, (Set_of_E.elements_spec1 D x),
       <-Set_of_E.add_spec, Set_of_E.elements_spec1; apply iff_refl.
   intros; ring.
   apply PermutP_map, PermutP_sym, PermutP_map.
   apply PermutP_weaken with eq; [ intros; subst; trivial | ].
   apply Permutation_PermutP, NoDup_Permutation.
     apply NoDup_cons.
       unfold is_true in H1; rewrite Set_of_E.mem_spec, <-Set_of_E.elements_spec1 in H1;
       intro H; apply H1; apply (In_InA E.eq_equiv H).
       apply (NoDupA_NoDup (Set_of_E.elements_spec2w _)).
     apply (NoDupA_NoDup (Set_of_E.elements_spec2w _)).
     intros; rewrite <- 2 InA_In.
     rewrite InA_cons, (Set_of_E.elements_spec1 D x),
       <-Set_of_E.add_spec, Set_of_E.elements_spec1; apply iff_refl.
 Qed.

 (* Specification of WSetOn seems incomplete *)
 Hypothesis Empty_elements: forall X,
   Set_of_E.Empty X -> Set_of_E.elements X = List.nil.

 Hypothesis is_empty_dec: forall (X:Set_of_E.t),
   {x:E.t | Set_of_E.In x X} + {Set_of_E.Empty X}.

 Parameter dummy: E.t.

 (* Pick an element [(x1,x2) in X1 x X2] with probability 
    proportional to [exp (-eps * cost (F - {x1} + {x2}, D))] *) 
 Definition pick_points (F D X1 X2: Set_of_E.t) (eps:R): Distr (E.t * E.t).
  intros.
  set (f := fun D' x => cost (Set_of_E.add (snd x) (Set_of_E.remove (fst x) F)) D').
  set (Out := list_prod (Set_of_E.elements X1) (Set_of_E.elements X2)).
  refine (@exp_antimon Set_of_E.t (E.t * E.t) eps f Out _ (dummy,dummy) D).
  unfold Out.
  destruct (is_empty_dec X1) as [ (x1,HX1) | HX1 ]; 
    [ | right; rewrite (Empty_elements HX1); simpl; trivial ].
  destruct (is_empty_dec X2) as [ (x2,HX2) | HX2 ]; 
    [ | right; rewrite (Empty_elements HX2) ;
      induction (Set_of_E.elements X1); simpl; trivial ].
  left; exists (x1,x2); rewrite in_prod_iff; 
    rewrite <-Set_of_E.elements_spec1, InA_In in *; split; trivial.
 Defined.

 Parameter eqU: E.t -> E.t -O-> U.
 Hypothesis eqU_spec: forall a:E.t, cover (eq a) (eqU a).

 Lemma pick_points_distance: forall (F D1 D2 X1 X2: Set_of_E.t) (eps:R),
   0 <= eps ->
   adj_sets D1 D2 ->
   let d1 := pick_points F D1 X1 X2 eps in
   let d2 := pick_points F D2 X1 X2 eps in
   let lam := exp (2 * eps * Diameter) in 
   le_dist d1 d2 lam D0.
 Proof.
  intros.
  refine (@exp_antimon_dist _ _ _  H _ _ _ (dummy,dummy) _ 
    (cover_eq_prod _ _ eqU_spec eqU_spec) _ _ _ _ _ _ _).
    intro; apply (in_dec (prod_dec E.eq_dec E.eq_dec)). 
    apply NoDup_list_prod; apply NoDupA_NoDup; 
      apply Set_of_E.elements_spec2w.
    intros; apply (cost_sensitivity _ H0).
    rewrite <-(Diam_spec dummy dummy), <-Delta_pos; trivial.
 Qed.


 (* Pick an index [i in [0...N-1]] with probability 
    proportional to [exp (-exp * cost (F i, D))] *)
 Definition pick_index (D:Set_of_E.t) (F:nat -> Set_of_E.t) (N:nat) (eps:R): Distr (nat).
  intros.
  set (f:= fun D' i => cost (F i) D').
  set (Out := seq 0 N).
  refine (@exp_antimon (@Set_of_E.t) nat eps f Out _ 0%nat D).
  unfold Out; destruct (zerop N); [ right; subst; trivial |
    left; exists 0%nat; apply le_In_seq; split; omega ].
 Defined.

 Lemma pick_index_distance: forall (D1 D2:Set_of_E.t) (F:nat -> Set_of_E.t) 
   (N:nat) (eps:R),
   0 <= eps ->
   adj_sets D1 D2 ->
   let d1 := pick_index D1 F N eps in
   let d2 := pick_index D2 F N eps in 
   let lam := exp (2 * eps * Diameter) in 
   le_dist d1 d2 lam D0.
 Proof.
  intros.
  refine (@exp_antimon_dist _ _ _  H _ _ _ (0%nat) _ 
    (fun b =>  cover_dec (eq_nat_dec b)) _ _ _ _ _ _ _).
    intro b; case_eq (leb N b); intro Heq.
      apply leb_complete in Heq; right; intro H'; apply In_seq_le in H'; omega.
      apply leb_complete_conv in Heq; left; apply le_In_seq; split; omega.
    apply NoDup_seq.
    intros; apply (cost_sensitivity _ H0).
    rewrite <-(Diam_spec dummy dummy), <-Delta_pos; trivial.
 Qed.

End QMetricExtension.



