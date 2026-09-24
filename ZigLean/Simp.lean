import ZigLean.SimpAttr
import ZigLean.Basic

attribute [zig_unfold] StateT.run' StateT.run bind pure StateT.bind StateT.pure StateT.map
  ExceptT.bind ExceptT.pure ExceptT.mk ExceptT.bindCont ExceptT.map Functor.map liftM monadLift
  MonadLift.monadLift StateT.lift throw throwThe MonadExcept.throw MonadExceptOf.throw ExceptT.lift
  Option.bind get getThe MonadState.get MonadStateOf.get StateT.get modify modifyGet
  MonadState.modifyGet MonadStateOf.modifyGet StateT.modifyGet Zig.call
