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
