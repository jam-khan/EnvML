module EnvML.Errors where

-- | Represents errors that can occur during type expansion.
data TypeExpansionError
    = -- | Type alias not found in the context.
      AliasNotFound String
    | -- | Multiple types with same alias detected (Not allowed).
      DuplicateAlias String
    | -- | If typing context is not well formed with intersection types
      TypeContextError String
    | -- | Type expansion failed at the term level.
      TypeExpansionFailed String
    deriving (Show)

-- | Represents errors that can occur during the pretty printing of the surface level AST.
newtype SurfacePrettyPrintError
    = -- | Simple print failure
      PrettyPrintFailed String

-- | IMPORTANT: Description not completed
data LocallyNamelessError
    = -- | Potential misuse
      ScopeError String
    | ParamError String
    | -- | Failed while resolving de-bruijn indices
      DebruijnFailed String
    | LocallyNamelessFailed String
    deriving (Show)

-- | IMPORTANT: Description not completed
newtype DesugarError = DesugarFailed String
    deriving (Show)

-- | Interpreter error
newtype InterpreterError = InterpreterFailed String
    deriving (Show)

-- | Represents type errors detected at the source level.
newtype SourceTypeError = STypeError String
    deriving (Eq, Show)

-- | Represents errors for separate compilation.
newtype SeparateCompilationError = SepCompError String
    deriving (Show)
