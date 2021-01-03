||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016, 2019
module Network.Socket

import public Network.Socket.Data
import Network.Socket.Raw
import Data.List
import System.FFI

idrisSocketClass : String
idrisSocketClass = "io/github/mmhelloworld/idris2boot/runtime/IdrisSocket"

-- ----------------------------------------------------- [ Network Socket API. ]
%foreign
    jvm' idrisSocketClass "create" "int int int" idrisSocketClass
prim_createSocket : Int -> Int -> Int -> PrimIO SocketDescriptor

%foreign
    jvm' idrisSocketClass ".close" idrisSocketClass "void"
prim_closeSocket : AnyPtr -> PrimIO ()

%foreign
    jvm' idrisSocketClass ".bind"
        "io/github/mmhelloworld/idris2boot/runtime/IdrisSocket int int java/lang/String int" "int"
prim_bindSocket : AnyPtr -> Int -> Int -> String -> Int -> PrimIO Int

%foreign
    jvm' idrisSocketClass ".connect"
        "io/github/mmhelloworld/idris2boot/runtime/IdrisSocket int int java/lang/String int" "int"
prim_connectSocket : AnyPtr -> Int -> Int -> String -> Int -> PrimIO Int

%foreign
    jvm' idrisSocketClass ".listen" "io/github/mmhelloworld/idris2boot/runtime/IdrisSocket int" "int"
prim_listenSocket : AnyPtr -> Int -> PrimIO Int

%foreign
    jvm' idrisSocketClass ".accept"
        "io/github/mmhelloworld/idris2boot/runtime/IdrisSocket java/lang/Object" idrisSocketClass
prim_acceptSocket : AnyPtr -> AnyPtr -> PrimIO SocketDescriptor

%foreign
    jvm idrisSocketClass "createSocketAddress"
prim_createSocketAddress : PrimIO AnyPtr

||| Creates a UNIX socket with the given family, socket type and protocol
||| number. Returns either a socket or an error.
export
socket : (fam  : SocketFamily)
      -> (ty   : SocketType)
      -> (pnum : ProtocolNumber)
      -> IO (Either SocketError Socket)
socket sf st pn = do
  socket_res <- primIO $ prim_createSocket (toCode sf) (toCode st) pn
  errorNumber <- getErrno
  if errorNumber /= 0
    then pure $ Left errorNumber
    else pure $ Right (MkSocket socket_res sf st pn)

||| Close a socket
export
close : Socket -> IO ()
close sock = primIO $ prim_closeSocket (descriptor sock)

||| Binds a socket to the given socket address and port.
||| Returns 0 on success, an error code otherwise.
export
bind : (sock : Socket)
    -> (addr : Maybe SocketAddress)
    -> (port : Port)
    -> IO Int
bind sock addr port = do
    bind_res <- primIO $ prim_bindSocket (descriptor sock) (toCode $ family sock) (toCode $ socketType sock)
        (saString addr) port
    if bind_res == (-1)
      then getErrno
      else pure 0
  where
    saString : Maybe SocketAddress -> String
    saString (Just sa) = show sa
    saString Nothing   = ""

||| Connects to a given address and port.
||| Returns 0 on success, and an error number on error.
export
connect : (sock : Socket)
       -> (addr : SocketAddress)
       -> (port : Port)
       -> IO ResultCode
connect sock addr port = do
  conn_res <- primIO $ prim_connectSocket (descriptor sock) (toCode $ family sock) (toCode $ socketType sock)
    (show addr) port
  if conn_res == (-1)
    then getErrno
    else pure 0

||| Listens on a bound socket.
|||
||| @sock The socket to listen on.
export
listen : (sock : Socket) -> IO Int
listen sock = do
  listen_res <- primIO $ prim_listenSocket (descriptor sock) BACKLOG
  if listen_res == (-1)
    then getErrno
    else pure 0

||| Accept a connection on the provided socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success a pairing of:
||| + `Socket`        :: The socket representing the connection.
||| + `SocketAddress` :: The
|||
||| @sock The socket used to establish connection.
export
accept : (sock : Socket)
      -> IO (Either SocketError (Socket, SocketAddress))
accept sock = do

  -- We need a pointer to a sockaddr structure. This is then passed into
  -- idrnet_accept and populated. We can then query it for the SocketAddr and free it.

  sockaddr_ptr <- primIO prim_createSocketAddress

  accept_res <- primIO $ prim_acceptSocket (descriptor sock) sockaddr_ptr
  errorNumber <- getErrno
  if errorNumber /= 0
    then pure $ Left errorNumber
    else do
      let (MkSocket _ fam ty p_num) = sock
      sockaddr <- getSockAddr (SAPtr sockaddr_ptr)
      sockaddr_free (SAPtr sockaddr_ptr)
      pure $ Right ((MkSocket accept_res fam ty p_num), sockaddr)

%foreign
    jvm' idrisSocketClass ".send"
        "io/github/mmhelloworld/idris2boot/runtime/IdrisSocket java/lang/String" "int"
prim_sendSocket : SocketDescriptor -> String -> PrimIO Int

||| Send data on the specified socket.
|||
||| Returns on failure a `SocketError`.
||| Returns on success the `ResultCode`.
|||
||| @sock The socket on which to send the message.
||| @msg  The data to send.
export
send : (sock : Socket)
    -> (msg  : String)
    -> IO (Either SocketError ResultCode)
send sock dat = do
  send_res <- primIO $ prim_sendSocket (descriptor sock) dat

  if send_res == (-1)
    then map Left getErrno
    else pure $ Right send_res

%foreign
    jvm' idrisSocketClass ".receive"
        "io/github/mmhelloworld/idris2boot/runtime/IdrisSocket int" "java/lang/String"
prim_receiveSocket : SocketDescriptor -> Int -> PrimIO String

||| Receive data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success a pairing of:
||| + `String`     :: The payload.
||| + `ResultCode` :: The result of the underlying function.
|||
||| @sock The socket on which to receive the message.
||| @len  How much of the data to receive.
export
recv : (sock : Socket)
    -> (len : ByteLength)
    -> IO (Either SocketError (String, ResultCode))
recv sock len = do
  -- Firstly make the request, get some kind of recv structure which
  -- contains the result of the recv and possibly the retrieved payload
  payload <- primIO $ prim_receiveSocket (descriptor sock) len
  errorNumber <- getErrno
  if errorNumber /= 0
    then pure $ Left errorNumber
    else pure $ Right (payload, len)

||| Receive all the remaining data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success the payload `String`
|||
||| @sock The socket on which to receive the message.
export
recvAll : (sock : Socket) -> IO (Either SocketError String)
recvAll sock = recvRec sock [] 64
  where
    partial
    recvRec : Socket -> List String -> ByteLength -> IO (Either SocketError String)
    recvRec sock acc n = do res <- recv sock n
                            case res of
                              Left 0 => pure (Right $ concat $ reverse acc)
                              Left c => pure (Left c)
                              Right (str, _) => let n' = min (n * 2) 65536 in
                                                recvRec sock (str :: acc) n'

||| Send a message.
|||
||| Returns on failure a `SocketError`
||| Returns on success the `ResultCode`
|||
||| @sock The socket on which to send the message.
||| @addr Address of the recipient.
||| @port The port on which to send the message.
||| @msg  The message to send.
export
sendTo : (sock : Socket)
      -> (addr : SocketAddress)
      -> (port : Port)
      -> (msg  : String)
      -> IO (Either SocketError ByteLength)
sendTo sock addr p dat = do
  sendto_res <- cCall Int "idrnet_sendto"
                [ descriptor sock, dat, show addr, p ,toCode $ family sock ]

  if sendto_res == (-1)
    then map Left getErrno
    else pure $ Right sendto_res

||| Receive a message.
|||
||| Returns on failure a `SocketError`.
||| Returns on success a triple of
||| + `UDPAddrInfo` :: The address of the sender.
||| + `String`      :: The payload.
||| + `Int`         :: Result value from underlying function.
|||
||| @sock The channel on which to receive.
||| @len  Size of the expected message.
|||
export
recvFrom : (sock : Socket)
        -> (len  : ByteLength)
        -> IO (Either SocketError (UDPAddrInfo, String, ResultCode))
recvFrom sock bl = do
  recv_ptr <- cCall AnyPtr "idrnet_recvfrom"
              [ descriptor sock, bl ]

  let recv_ptr' = RFPtr recv_ptr
  isNull <- (nullPtr recv_ptr)
  if isNull
    then map Left getErrno
    else do
      result <- cCall Int "idrnet_get_recvfrom_res" [ recv_ptr ]
      if result == -1
        then do
          freeRecvfromStruct recv_ptr'
          map Left getErrno
        else do
          payload <- foreignGetRecvfromPayload recv_ptr'
          port <- foreignGetRecvfromPort recv_ptr'
          addr <- foreignGetRecvfromAddr recv_ptr'
          freeRecvfromStruct recv_ptr'
          pure $ Right (MkUDPAddrInfo addr port, payload, result)
