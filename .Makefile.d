src/Stm.vo src/Stm.glob src/Stm.v.beautified src/Stm.required_vo: src/Stm.v 
src/Stm.vio: src/Stm.v 
src/Stm.vos src/Stm.vok src/Stm.required_vos: src/Stm.v 
src/FStep.vo src/FStep.glob src/FStep.v.beautified src/FStep.required_vo: src/FStep.v src/Stm.vo
src/FStep.vio: src/FStep.v src/Stm.vio
src/FStep.vos src/FStep.vok src/FStep.required_vos: src/FStep.v src/Stm.vos
