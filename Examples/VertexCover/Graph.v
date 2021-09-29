Require Import BoolEquality.
Require Import MSets.

Set Implicit Arguments.

Unset Strict Implicit.


Module Type GRAPH.

 Parameter t : Type.

 Parameter vertex : Type.

 Declare Module E : DecidableType with Definition t := vertex.
 
 Declare Module WS : WSetsOn E.
 
 Parameter V : t -> WS.t.
 
 Parameter eqb : t -> t -> bool.

 Parameter eqb_spec : forall (g1 g2:t), if eqb g1 g2 then g1 = g2 else g1 <> g2.

 Parameter v_eqb : vertex -> vertex -> bool.

 Parameter v_eqb_spec : forall (v1 v2:vertex),
  if v_eqb v1 v2 then v1 = v2 else v1 <> v2.

 Parameter empty : t.

 Parameter dummy_vertex : vertex.

 Parameter in_graph : t -> vertex -> bool.

 Parameter in_graph_edge : t -> vertex -> vertex -> bool.

 Parameter is_empty : t -> bool.

 Parameter size : t -> nat.

 Parameter weight : t -> nat.
 
 Parameter degree : t -> vertex -> nat.

 Parameter remove_vertex : t -> vertex -> t.

 Parameter not_is_empty : forall g, ~is_empty g -> {v | in_graph g v}.

 Parameter is_empty_size : forall G, is_empty G -> size G = O.

 Parameter size_1_inversion : forall G,
  size G = 1 -> forall x y, in_graph G x -> in_graph G y -> x = y.

 Parameter in_graph_element : forall (G:t) x,
  in_graph G x <-> In x (WS.elements (V G)).

 Parameter NoDup_elements : forall G, NoDup (WS.elements (V G)).

 Parameter size_elements : forall G, length (WS.elements (V G)) = size G.

 Parameter weight_def : forall G,
  weight G = fold_right plus O (map (degree G) (WS.elements (V G))).

 Parameter degree_le_weight : forall G x, 2 * degree G x <= weight G.
 
 Parameter size_eq : forall G1 G2,
  (forall x, in_graph G1 x = in_graph G2 x) ->
  size G1 = size G2.

 Parameter remove_vertex_size : forall (G:t) (v:vertex),
  in_graph G v -> size (remove_vertex G v) = pred (size G).

 Parameter remove_vertex_eq : forall G x, ~in_graph (remove_vertex G x) x.

 Parameter remove_vertex_neq : forall G x v, 
  x <> v -> in_graph G v = in_graph (remove_vertex G x) v.

 Parameter in_graph_remove_vertex : forall G G', 
  (forall x, in_graph G x = in_graph G' x) ->
  forall v x, in_graph (remove_vertex G v) x = in_graph (remove_vertex G' v) x.

 Parameter extensionality : forall G1 G2,
  (forall x, in_graph G1 x = in_graph G2 x) ->
  (forall x y, in_graph_edge G1 x y = in_graph_edge G2 x y) ->
  G1 = G2.

 Parameter in_graph_edge_sym : forall G v v', 
  in_graph_edge G v v' = in_graph_edge G v' v.

 Parameter edge_vertex : forall G v v', 
  in_graph_edge G v v'-> in_graph G v /\ in_graph G v'.
 
 Parameter in_graph_remove_edge_neq: forall G v v' x,
  in_graph_edge G v v' ->
  x <> v ->
  x <> v' -> 
  in_graph_edge (remove_vertex G x) v v'.

 Parameter in_graph_remove_edge_conv : forall G v v' x,
  in_graph_edge (remove_vertex G x) v v' -> in_graph_edge G v v'.

 Parameter weight_diff : forall G1 G2 t_ u_,
  G1 <> G2 ->
  (forall x, in_graph G1 x = in_graph G2 x) ->
  in_graph_edge G2 t_ u_ ->
  (forall x y, in_graph_edge G2 x y -> 
   in_graph_edge G1 x y \/ (x = t_ /\ y = u_) \/ (x = u_ /\ y = t_)) ->
  (forall x y, in_graph_edge G1 x y -> in_graph_edge G2 x y) -> 
  (weight G1 + 2 = weight G2)%nat.

 Parameter degree_diff_neq : forall G1 G2 t_ u_,
  (forall x, in_graph G1 x = in_graph G2 x) ->
  in_graph_edge G2 t_ u_ ->
  (forall x y, in_graph_edge G2 x y -> 
   in_graph_edge G1 x y \/ (x = t_ /\ y = u_) \/ (x = u_ /\ y = t_)) -> 
  (forall x y, in_graph_edge G1 x y -> in_graph_edge G2 x y) -> 
  forall a, a <> t_ -> a <> u_ -> degree G1 a = degree G2 a.

 Parameter degree_diff_eq : forall G1 G2 t_ u_,
  G1 <> G2 ->
  (forall x, in_graph G1 x = in_graph G2 x) ->
  in_graph_edge G2 t_ u_ ->
  (forall x y, in_graph_edge G2 x y -> 
   in_graph_edge G1 x y \/ (x = t_ /\ y = u_) \/ (x = u_ /\ y = t_)) ->
  (forall x y, in_graph_edge G1 x y -> in_graph_edge G2 x y) -> 
  degree G2 t_ = S (degree G1 t_) /\ degree G2 u_ = S (degree G1 u_).

 Parameter remove_vertex_diff_1 : forall G1 G2 u v,
  (forall x, in_graph G1 x = in_graph G2 x) ->
  (forall x y, in_graph_edge G1 x y -> in_graph_edge G2 x y) ->
  in_graph_edge G2 u v /\
  (forall x y,
   in_graph_edge G2 x y ->
   in_graph_edge G1 x y \/ x = u /\ y = v \/ x = v /\ y = u) ->
  remove_vertex G1 u = remove_vertex G2 u.

End GRAPH.
