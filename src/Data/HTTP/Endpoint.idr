module Data.HTTP.Endpoint

import Data.Buffer.Indexed
import Data.ByteString
import JSON
import Network.HTTP.Application
import Network.HTTP.Connection
import Network.HTTP.Headers
import Network.HTTP.Methods
import Network.HTTP.Request
import Network.HTTP.Response
import Network.Socket


data Handler : Type -> Type where
  Fallback : Application -> Handler a
  Getter : IO (Maybe a) -> Handler a
  Putter : (a -> IO a) -> Handler a


public export
data Endpoint : Type -> Type -> Type where
  Ep : List (Method, Handler a) -> b -> Endpoint a b

public export
Functor (Endpoint a) where
  map f (Ep handlers b) = Ep handlers (f b)

public export
Applicative (Endpoint a) where
  pure b = Ep [] b
  (Ep handlers f) <*> (Ep handlers' b) = Ep (handlers' ++ handlers) (f b)

public export
Monad (Endpoint a) where
  (Ep handlers b) >>= f = let (Ep handlers' b') = f b in Ep (handlers' ++ handlers) b'


epHandler : List (Method, Handler a) -> Method -> Maybe (Handler a)
epHandler [] _ = Nothing
epHandler ((m, h) :: hs) m' = if m == m' then Just h else epHandler hs m'


public export
endpointHandler : (FromJSON a, ToJSON a) => Endpoint a () -> Application
endpointHandler (Ep handlers ()) request respond =
  case epHandler handlers request.method of
    Just (Fallback app) =>
      app request respond
    Just (Getter ep) => do
      maybeResource <- ep
      case maybeResource of
        Nothing =>
          respond $ MkResponse statusNotFound empty "Not found\n"
        Just resource =>
          respond $ MkResponse statusOK empty $ fromString $ encode resource
    Just (Putter ep) => do
      Right content <- readRequestBody request
      | Left err => respond $ MkResponse statusBadRequest empty "Read request error\n"
      Right resource <- pure $ decode $ toString content
      | Left err => respond $ MkResponse statusBadRequest empty "Invalid JSON\n"
      resource' <- ep resource
      respond $ MkResponse statusOK empty $ fromString $ encode resource'
    _ =>
      respond $ MkResponse statusMethodNotAllowed empty "Method not allowed\n"


public export
delete : IO (Maybe a) -> Endpoint a ()
delete ep = Ep [(DELETE, Getter ep)] ()


public export
get : IO (Maybe a) -> Endpoint a ()
get ep = Ep [(GET, Getter ep)] ()


public export
post : (a -> IO a) -> Endpoint a ()
post ep = Ep [(POST, Putter ep)] ()


public export
put : (a -> IO a) -> Endpoint a ()
put ep = Ep [(PUT, Putter ep)] ()
