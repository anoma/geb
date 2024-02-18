module LanguageDef.MLQuivUniv

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.Quiver
import LanguageDef.MLQuivCat

-----------------------------------------
-----------------------------------------
---- Universal properties of quivers ----
-----------------------------------------
-----------------------------------------

----------------------------------------------
---- Internal to and enriched over `Type` ----
----------------------------------------------

public export
TypeQuivInit : TypeQuivV Void
TypeQuivInit (v, _) = void v

public export
TypeQuivInitSL : TypeRQuivSL {v=Void} TypeQuivInit
TypeQuivInitSL v = void v

public export
TypeQuivInitComp : TypeCQuivComp {v=Void} TypeQuivInit
TypeQuivInitComp v = void v

public export
TypeQuivTerm : TypeQuivV Unit
TypeQuivTerm ((), ()) = Unit

public export
TypeQuivTermSL : TypeRQuivSL {v=Unit} TypeQuivTerm
TypeQuivTermSL () = ()

public export
TypeQuivTermComp : TypeCQuivComp {v=Unit} TypeQuivTerm
TypeQuivTermComp () () () () () = ()

public export
data TypeQuivCoprodV : {0 v, w : Type} ->
    TypeQuivV v -> TypeQuivV w -> TypeQuivV (Either v w) where
  TQCl : {0 v, w : Type} -> (qv : TypeQuivV v) -> (qw : TypeQuivV w) ->
    (x, y : v) -> qv (x, y) -> TypeQuivCoprodV qv qw (Left x, Left y)
  TQCr : {0 v, w : Type} -> (qv : TypeQuivV v) -> (qw : TypeQuivV w) ->
    (x, y : w) -> qw (x, y) -> TypeQuivCoprodV qv qw (Right x, Right y)

public export
TypeRQuivSLCoprod : {0 v, w : Type} ->
  {qv : TypeQuivV v} -> {qw : TypeQuivV w} ->
  TypeRQuivSL {v} qv -> TypeRQuivSL {v=w} qw ->
  TypeRQuivSL {v=(Either v w)} (TypeQuivCoprodV qv qw)
TypeRQuivSLCoprod {v} {w} {qv} {qw} slv slw evw = case evw of
  Left ev => TQCl {v} {w} qv qw ev ev $ slv ev
  Right ew => TQCr {v} {w} qv qw ew ew $ slw ew

public export
TypeCQuivCompCoprod : {0 v, w : Type} ->
  {qv : TypeQuivV v} -> {qw : TypeQuivV w} ->
  TypeCQuivComp {v} qv -> TypeCQuivComp {v=w} qw ->
  TypeCQuivComp {v=(Either v w)} (TypeQuivCoprodV qv qw)
TypeCQuivCompCoprod {v} {w} {qv} {qw} cv cw (Left ev) (Left ev') (Left ev'')
  (TQCl qv qw ev' ev'' eqv) (TQCl qv qw ev ev' eqv') =
    TQCl {v} {w} qv qw ev ev'' $ cv ev ev' ev'' eqv eqv'
TypeCQuivCompCoprod {v} {w} {qv} {qw} cv cw (Right ew) (Right ew') (Right ew'')
  (TQCr qv qw ew' ew'' eqw) (TQCr qv qw ew ew' eqw') =
    TQCr {v} {w} qv qw ew ew'' $ cw ew ew' ew'' eqw eqw'

public export
TypeQuivEndBase : {v : Type} -> (v -> v -> Type) -> Type
TypeQuivEndBase {v} p = (ev : v) -> p ev ev

public export
TypeQuivProdP : {v : Type} -> (q : TypeQuivV v) -> (v -> v -> Type) -> Type
TypeQuivProdP {v} q p = (ev, ev' : v) -> q (ev, ev') -> p ev ev'

public export
TypeQuivCoendBase : {v : Type} -> (v -> v -> Type) -> Type
TypeQuivCoendBase {v} p = (ev : v ** p ev ev)

public export
TypeQuivSumP : {v : Type} -> (q : TypeQuivV v) -> (v -> v -> Type) -> Type
TypeQuivSumP {v} q p = (ev : v ** ev' : v ** (q (ev', ev), p ev ev'))

-- This is the profunctor underlying both the left and right Kan extensions of
-- a copresheaf, as described by a quiver internal to and enriched over `Type`,
-- along the constant functor from the index category to the terminal object of
-- `Type` (i.e. `Unit`).  The reason that the same profunctor underlies both
-- directions of Kan extension is that when extending a copresheaf `P` along
-- the constant functor to the terminal object, the left-extension profunctor
-- is effectively `1 x P` while the right-extension profunctor is effectively
-- `P ^ 1`, both of which are isomorphic to just `P`.
public export
TypeQuivKanExtProf : {v : Type} -> (slv : SliceObj v) -> v -> v -> Type
TypeQuivKanExtProf {v} slv _ = slv

public export
TypeQuivKanExtProfDimap :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv ->
  TypeQuivDimapSig {v} q (TypeQuivKanExtProf {v} slv)
TypeQuivKanExtProfDimap {v} q slv fm a b c d mca mbd slvb = fm b d mbd slvb

public export
TypeQuivKanExtProfLmap :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv ->
  TypeQuivLmapSig {v} q (TypeQuivKanExtProf {v} slv)
TypeQuivKanExtProfLmap {v} q slv fm a b c mba = id {a=(slv c)}

public export
TypeQuivKanExtProfRmap :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv ->
  TypeQuivRmapSig {v} q (TypeQuivKanExtProf {v} slv)
TypeQuivKanExtProfRmap {v} q slv fm a b c mab = fm a b mab

public export
TypeQuivRKanExtBase : {v : Type} -> (slv : SliceObj v) -> Type
TypeQuivRKanExtBase {v} slv =
  TypeQuivEndBase {v} (TypeQuivKanExtProf {v} slv)

public export
TypeQuivRKanProdP : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivRKanProdP {v} q slv = TypeQuivProdP {v} q (TypeQuivKanExtProf {v} slv)

public export
TypeQuivRKanExt :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv -> Type
TypeQuivRKanExt {v} q slv fm =
  (pi : ((ev : v) -> slv ev) **
   (ev, ev' : v) -> (f : q (ev, ev')) -> fm ev ev' f (pi ev) = pi ev')

public export
TypeQuivLKanExtBase : {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv -> Type
TypeQuivLKanExtBase {v} q slv fm =
  TypeQuivCoendBase {v} (TypeQuivKanExtProf {v} slv)

public export
TypeQuivLKanSumP : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivLKanSumP {v} q slv = TypeQuivSumP {v} q (TypeQuivKanExtProf {v} slv)
