module Data.HTTP.Router

import Data.Buffer.Indexed
import Data.ByteString
import Data.IORef
import Data.List1
import Data.String
import Network.HTTP.Application
import Network.HTTP.Connection
import Network.HTTP.Headers
import Network.HTTP.Request
import Network.HTTP.Response


infixr 5 </>
infixr 5 <||>


public export
data Path : Type where
  CaptureRemaining : String -> Path
  CaptureSegment : {a : Type} -> String -> (String -> Maybe a) -> Path -> Path
  MatchSegment : String -> Path -> Path
  RootPath : Path
  SubPaths : Path


public export
(</>) : String -> Path -> Path
(</>) = MatchSegment


public export
handlerType : Path -> Type
handlerType RootPath = Application
handlerType SubPaths = Application
handlerType (CaptureRemaining _) = List String -> Application
handlerType (CaptureSegment {a} _ _ rest) = a -> handlerType rest
handlerType (MatchSegment _ rest) = handlerType rest


handlerNotFound : Application
handlerNotFound request respond =
  respond $ MkResponse statusNotFound empty "Not found\n"


public export
data Route : (match : Path) -> Type where
  Handler : {match : _} -> handlerType match -> Route match


public export
data Router : Type where
  RouteAlternative : Router -> Router -> Router
  RoutePath : Route match -> Router


public export
(<||>) : Router -> Router -> Router
(<||>) = RouteAlternative


matchPath : (path : Path) -> List String -> handlerType path -> Maybe Application
matchPath RootPath [] handler = Just handler
matchPath RootPath _ _ = Nothing
matchPath SubPaths _ handler = Just handler
matchPath (CaptureRemaining _) path handler = Just $ handler path
matchPath (CaptureSegment _ parse rest) (a :: path) handler =
  case parse a of
    Just a => matchPath rest path (handler a)
    Nothing => Nothing
matchPath (CaptureSegment _ _ _) [] _ = Nothing
matchPath (MatchSegment a rest) (b :: path) handler =
  if a == b
    then matchPath rest path handler
    else Nothing
matchPath (MatchSegment _ _) [] _ = Nothing


resolveHandler : Route match -> List String -> Maybe Application
resolveHandler (Handler {match} handler) path = matchPath match path handler


resolveRoute : Router -> List String -> Maybe Application
resolveRoute (RouteAlternative a b) path =
  resolveRoute a path <|> resolveRoute b path
resolveRoute (RoutePath route) path =
  resolveHandler route path


public export
route : Router -> Application
route router request respond =
  case resolveRoute router path of
    Just handler => handler request respond
    Nothing => handlerNotFound request respond
  where
    fixPath : List1 String -> List String
    fixPath ("" ::: rest) = rest
    fixPath (a ::: rest) = a :: rest
    path : List String
    path = fixPath $ split (== '/') request.resource
