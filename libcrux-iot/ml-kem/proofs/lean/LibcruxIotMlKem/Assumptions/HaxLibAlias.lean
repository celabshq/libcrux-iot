-- Hand-written. `libcrux-iot-ml-kem`'s dependency graph carries THREE `hax-lib`
-- crate versions (its own 0.4.0-rc.2, the `hacspec_ml_kem` spec's 0.3.7, and
-- `libcrux-secrets`' 0.3.6). charon names duplicated crates `hax_lib`,
-- `hax_lib_1`, …; as of hax v0.4.0 the copy this crate's `matrix.rs` refers to
-- (`hax_lib::prop::*`, used by the `poly_matches`/`vec_matches` matching
-- predicates) comes out as `hax_lib_1`, while the Lean `CoreModels` only model
-- `hax_lib`. Unifying the versions is not possible locally (the extra copies are
-- pinned by external crates), so alias the five referenced symbols instead.
-- Reducible `abbrev`s keep them definitionally equal to the real models.
import CoreModels
import Hax

namespace hax_lib_1.prop

abbrev «Prop» : Type := hax_lib.prop.Prop
abbrev «forall» := @hax_lib.prop.«forall»

namespace «Prop»
abbrev from_bool := hax_lib.prop.Prop.from_bool
abbrev and := @hax_lib.prop.Prop.and
namespace Insts
abbrev CoreConvertFromBool := hax_lib.prop.Prop.Insts.CoreConvertFromBool
end Insts
end «Prop»

end hax_lib_1.prop

-- hax also emits the mangled crate name UNDER the `hax_lib` prefix for some
-- instance arguments (e.g. `hax_lib.hax_lib_1.prop.Prop.Insts.CoreConvertFromBool`);
-- alias those forms too.
namespace hax_lib
namespace hax_lib_1.prop.Prop.Insts
abbrev CoreConvertFromBool := hax_lib.prop.Prop.Insts.CoreConvertFromBool
end hax_lib_1.prop.Prop.Insts
end hax_lib
