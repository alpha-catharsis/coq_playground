src/Stm.vo src/Stm.glob src/Stm.v.beautified src/Stm.required_vo: src/Stm.v 
src/Stm.vio: src/Stm.v 
src/Stm.vos src/Stm.vok src/Stm.required_vos: src/Stm.v 
src/Step.vo src/Step.glob src/Step.v.beautified src/Step.required_vo: src/Step.v src/Stm.vo
src/Step.vio: src/Step.v src/Stm.vio
src/Step.vos src/Step.vok src/Step.required_vos: src/Step.v src/Stm.vos
src/Seq.vo src/Seq.glob src/Seq.v.beautified src/Seq.required_vo: src/Seq.v src/Stm.vo src/Step.vo
src/Seq.vio: src/Seq.v src/Stm.vio src/Step.vio
src/Seq.vos src/Seq.vok src/Seq.required_vos: src/Seq.v src/Stm.vos src/Step.vos
src/Path.vo src/Path.glob src/Path.v.beautified src/Path.required_vo: src/Path.v src/Stm.vo src/Step.vo src/Seq.vo
src/Path.vio: src/Path.v src/Stm.vio src/Step.vio src/Seq.vio
src/Path.vos src/Path.vok src/Path.required_vos: src/Path.v src/Stm.vos src/Step.vos src/Seq.vos
