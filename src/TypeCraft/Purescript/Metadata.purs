module TypeCraft.Purescript.MD where

import Prelude

-- Type Meta- Data
type ArrowMD = { codIndented :: Boolean }
type TypeArgMD = { indented :: Boolean }
type TNeuMD = {}
type TAppMD = { argIndented :: Boolean }
type THoleMD = {}
type TLambdaMD = { bodyIndented :: Boolean }

-- Term Meta- Data
type LambdaMD = { bodyIndented :: Boolean }
type AppMD = { argIndented :: Boolean }
type LetMD
  = { varIndented :: Boolean
    , typeIndented :: Boolean
    , defIndented :: Boolean
    , bodyIndented :: Boolean
    }
type GADTMD = { varIndented :: Boolean, bodyIndented :: Boolean}
type TermBindMD = { varName :: String }
type TypeBindMD = { varName :: String}
type CtrMD = { indented :: Boolean } -- refers to if the constructor is indented within its parent list of constructors
type CtrParamMD = { paramName :: String, indented :: Boolean }
type TypeBoundaryMD = {}
type ContextBoundaryMD = {}
type HoleMD = {}
type BufferMD = {}
type VarMD = {}
type TLetMD = {}

-- no kind metadata because it is never in the source code
------------------------------------------------------------------------------------------------------------------------
--- Readable things above, garbage below -------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------
-- Default values for metadata
-- Type metadata defaults
defaultArrowMD :: ArrowMD
defaultArrowMD = { codIndented: false }

defaultTAppMD :: TAppMD
defaultTAppMD = { argIndented: false }

defaultTNeuMD :: TNeuMD
defaultTNeuMD = {}

defaultTypeArgMD :: TypeArgMD
defaultTypeArgMD = { indented: false }

defaultTHoleMD :: THoleMD
defaultTHoleMD = {}

defaultTLambdaMD :: TLambdaMD
defaultTLambdaMD = { bodyIndented: false }

defaultTLetMD :: TLetMD
defaultTLetMD = {}

-- Term metadata defaults
defaultHoleMD :: HoleMD
defaultHoleMD = {}

defaultTypeBoundaryMD :: TypeBoundaryMD
defaultTypeBoundaryMD = {}

defaultAppMD :: AppMD
defaultAppMD = { argIndented: false }

defaultBufferMD :: BufferMD
defaultBufferMD = {}

defaultVarMD :: VarMD
defaultVarMD = {}

defaultLambdaMD :: LambdaMD
defaultLambdaMD = {bodyIndented : false}

defaultLetMD :: LetMD
defaultLetMD =
  { varIndented: false
  , typeIndented: false
  , defIndented: false
  , bodyIndented: true
  }

-- termbind
defaultTermBindMD :: TermBindMD
defaultTermBindMD = { varName: "placeholder" }

-- typebind
defaultTypeBindMD :: TypeBindMD
defaultTypeBindMD = { varName: "placeholder" }

defaultGADTMD :: GADTMD
defaultGADTMD = { varIndented: false, bodyIndented: true}

-- Constructor
defaultCtrMD :: CtrMD
defaultCtrMD = {indented: false}

-- CtrParam
defaultCtrParamMD :: CtrParamMD
defaultCtrParamMD = {paramName: "", indented: false}

defaultCtxBoundaryMD :: ContextBoundaryMD
defaultCtxBoundaryMD = {}