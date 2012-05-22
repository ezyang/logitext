{-# LANGUAGE PackageImports, DeriveDataTypeable #-}

module JSONGeneric where

import Data.Aeson hiding (toJSON, fromJSON, parseJSON)
import qualified Data.Aeson.Types as T
import Data.Generics
import Data.Text (pack, unpack)
import qualified Data.Vector as V
import Data.ByteString.Lazy (ByteString)
import qualified Data.Attoparsec.Lazy as L

import qualified Data.HashMap.Strict as H
import "mtl" Control.Monad.State.Strict
import Data.Aeson.Types hiding (FromJSON(..), ToJSON(..), fromJSON)
import Control.Applicative ((<$>))
import Control.Arrow (first)

import Test.QuickCheck (Arbitrary(..), oneof)

type T a = a -> Value

toJSON :: (Data a) => a -> Value
toJSON = toJSON_generic
         `ext1Q` list
         `extQ` (T.toJSON :: T Int)
         `extQ` (T.toJSON :: T String)
         `extQ` (T.toJSON :: T Bool)
         `extQ` (T.toJSON :: T ()) -- XXX not right...
  where
    list xs = Array . V.fromList . map toJSON $ xs

-- alternative generic encoding of algebraic data type, consistent
-- with Urweb's encoding
toJSON_generic :: (Data a) => a -> Value
toJSON_generic = generic
  where
        -- Generic encoding of an algebraic data type.
        generic a =
            case dataTypeRep (dataTypeOf a) of
                -- No constructor, so it must be an error value.  Code
                -- it anyway as Null.
                AlgRep []  -> Null
                -- Elide a single constructor and just code the arguments.
                -- (this is the json_record case)
                AlgRep [c] -> encodeArgs c (gmapQ toJSON a)
                -- For multiple constructors, make an object with a
                -- field name that is the constructor (except lower
                -- case) and the data is the arguments encoded.
                -- (this is the json_variant ==> json_record case)
                AlgRep _   -> encodeConstr (toConstr a) (gmapQ toJSON a)
                rep        -> err (dataTypeOf a) rep
           where
              err dt r = modError "toJSON" $ "not AlgRep " ++
                                  show r ++ "(" ++ show dt ++ ")"
        -- Encode variants as an object with the constructor
        -- name as the single field and the data as the value.
        encodeConstr c as = object [(constrString c, encodeArgs c as)]

        constrString = pack . showConstr

        -- No field names indicates either a value (1) or tuple (2+),
        -- which is shorthand for a record with numeric field names.
        -- Use an array if the are no field names, but elide singleton arrays,
        -- and use an object if there are field names.
        encodeArgs c = encodeArgs' (constrFields c)
        encodeArgs' [] [j] = j
        encodeArgs' [] js  = encodeArgs' (map show [(1::Int)..]) js
        encodeArgs' ns js  = object $ zip (map pack ns) js

type F a = Parser a

parseJSON :: (Data a) => Value -> Parser a
parseJSON j = parseJSON_generic j
             `ext1R` list
             -- fascinating, apparently you need this instance or it
             -- won't manage to parse it properly. But you don't need it
             -- for lists...
             `ext1R` vector
             `extR` (value :: F Int)
             `extR` (value :: F String)
             `extR` (value :: F Bool)
             `extR` (value :: F ()) -- XXX not right...
  where
    value :: (T.FromJSON a) => Parser a
    value = T.parseJSON j
    list :: (Data a) => Parser [a]
    list = V.toList <$> parseJSON j
    vector :: (Data a) => Parser (V.Vector a)
    vector = case j of
               Array js -> V.mapM parseJSON js
               _        -> myFail
    myFail = modFail "parseJSON" $ "bad data: " ++ show j

fromJSON :: (Data a) => Value -> Result a
fromJSON = parse parseJSON

parseJSON_generic :: (Data a) => Value -> Parser a
parseJSON_generic j = generic
  where
        typ = dataTypeOf $ resType generic
        generic = case dataTypeRep typ of
                    AlgRep []  -> case j of
                                    Null -> return (modError "parseJSON" "empty type")
                                    _ -> modFail "parseJSON" "no-constr bad data"
                    AlgRep [_] -> decodeArgs (indexConstr typ 1) j
                    AlgRep _   -> do (c, j') <- getConstr typ j; decodeArgs c j'
                    rep        -> modFail "parseJSON" $
                                  show rep ++ "(" ++ show typ ++ ")"
        getConstr t (Object o) | [(s, j')] <- fromJSObject o = do
                                                c <- readConstr' t s
                                                return (c, j')
        getConstr _ _ = modFail "parseJSON" "bad constructor encoding"
        readConstr' t s =
          maybe (modFail "parseJSON" $ "unknown constructor: " ++ s ++ " " ++
                         show t)
                return $ readConstr t s

        decodeArgs c0 = go (numConstrArgs (resType generic) c0) c0
                           (constrFields c0)
         where
          go 0 c []       _          = construct c [] -- nullary constructor
          go 1 c []       jd         = construct c [jd] -- unary constructor
          go d c []       jd         = go d c (map show [1..d]) jd
          go _ c fs@(_:_) (Object o) = selectFields o fs >>=
                                       construct c -- field names
          go _ c _        jd         = modFail "parseJSON" $
                                       "bad decodeArgs data " ++ show (c, jd)

        fromJSObject = map (first unpack) . H.toList

        -- Build the value by stepping through the list of subparts.
        construct c = evalStateT $ fromConstrM f c
          where f :: (Data a) => StateT [Value] Parser a
                f = do js <- get
                       case js of
                         [] -> lift $ modFail "construct" "empty list"
                         (j':js') -> do put js'; lift $ parseJSON j'

        -- Select the named fields from a JSON object.
        selectFields fjs = mapM $ \f ->
           maybe (modFail "parseJSON" $ "field does not exist " ++ f) return $
             H.lookup (pack f) fjs

        -- Count how many arguments a constructor has.  The value x is
        -- used to determine what type the constructor returns.
        numConstrArgs :: (Data a) => a -> Constr -> Int
        numConstrArgs x c = execState (fromConstrM f c `asTypeOf` return x) 0
          where f = do modify (+1); return undefined

        resType :: MonadPlus m => m a -> a
        resType _ = modError "parseJSON" "resType"

modFail :: (Monad m) => String -> String -> m a
modFail func err = fail $ "JSONGeneric." ++ func ++ ": " ++ err

modError :: String -> String -> a
modError func err = error $ "JSONGeneric." ++ func ++ ": " ++ err

genericToFromJSON :: (Arbitrary a, Eq a, Data a) => a -> Bool
genericToFromJSON x = case fromJSON . toJSON $ x of
                Error _ -> False
                Success x' -> x == x'

genericToFromJSONFoo :: Foo -> Bool
genericToFromJSONFoo = genericToFromJSON

decode :: Data a => ByteString -> Maybe a
decode s =
    case L.parse json' s of
        L.Done _ v -> case fromJSON v of
            Success a -> Just a
            _ -> Nothing
        _ -> Nothing


data Foo = Foo {
      fooInt :: [Maybe String]
      {-
    , fooUnit :: Qua ()
    , fooTuple :: (String, Int)
    -}
    } | Bar Int Int | Baz deriving (Show, Typeable, Data, Eq)

data Qua a = Tua a a deriving (Show, Typeable, Data, Eq)

instance Arbitrary Foo where
    --arbitrary = oneof [liftM3 Foo arbitrary arbitrary arbitrary, liftM3 Bar arbitrary arbitrary arbitrary, return Baz]
    arbitrary = oneof [liftM Foo arbitrary, liftM2 Bar arbitrary arbitrary, return Baz, liftM2 Bar arbitrary arbitrary, return Baz]

instance Arbitrary a => Arbitrary (Qua a) where
    arbitrary = liftM2 Tua arbitrary arbitrary
