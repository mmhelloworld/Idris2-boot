||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
||| Type-unsafe parts. Use Network.Socket for a safe variant.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016
module Idris.Socket.Raw

import public Idris.Socket.Data

%include C "idris_net.h"

%access public export

-- ---------------------------------------------------------------- [ Pointers ]

data RecvStructPtr     = RSPtr Ptr
data RecvfromStructPtr = RFPtr Ptr

data BufPtr = BPtr Ptr

data SockaddrPtr = SAPtr Ptr

-- ---------------------------------------------------------- [ Socket Utilies ]

||| Frees a given pointer
sock_free : BufPtr -> JVM_IO ()
sock_free (BPtr ptr) = foreign FFI_C "idrnet_free" (Ptr -> JVM_IO ()) ptr

sockaddr_free : SockaddrPtr -> JVM_IO ()
sockaddr_free (SAPtr ptr) = foreign FFI_C "idrnet_free" (Ptr -> JVM_IO ()) ptr

||| Allocates an amount of memory given by the ByteLength parameter.
|||
||| Used to allocate a mutable pointer to be given to the Recv functions.
sock_alloc : ByteLength -> JVM_IO BufPtr
sock_alloc bl = map BPtr $ foreign FFI_C "idrnet_malloc" (Int -> JVM_IO Ptr) bl

||| Retrieves a socket address from a sockaddr pointer
getSockAddr : SockaddrPtr -> JVM_IO SocketAddress
getSockAddr (SAPtr ptr) = do
  addr_family_int <- foreign FFI_C "idrnet_sockaddr_family"
                             (Ptr -> JVM_IO Int)
                             ptr

  -- ASSUMPTION: Foreign call returns a valid int
  assert_total (case getSocketFamily addr_family_int of
    Just AF_INET => do
      ipv4_addr <- foreign FFI_C "idrnet_sockaddr_ipv4"
                           (Ptr -> JVM_IO String)
                           ptr

      pure $ parseIPv4 ipv4_addr
    Just AF_INET6 => pure IPv6Addr
    Just AF_UNSPEC => pure InvalidAddress)

freeRecvStruct : RecvStructPtr -> JVM_IO ()
freeRecvStruct (RSPtr p) =
    foreign FFI_C "idrnet_free_recv_struct"
            (Ptr -> JVM_IO ())
            p

||| Utility to extract data.
freeRecvfromStruct : RecvfromStructPtr -> JVM_IO ()
freeRecvfromStruct (RFPtr p) =
    foreign FFI_C "idrnet_free_recvfrom_struct"
            (Ptr -> JVM_IO ())
            p

||| Sends the data in a given memory location
|||
||| Returns on failure a `SocketError`
||| Returns on success the `ResultCode`
|||
||| @sock The socket on which to send the message.
||| @ptr  The location containing the data to send.
||| @len  How much of the data to send.
sendBuf : (sock : Socket)
       -> (ptr  : BufPtr)
       -> (len  : ByteLength)
       -> JVM_IO (Either SocketError ResultCode)
sendBuf sock (BPtr ptr) len = do
  send_res <- foreign FFI_C "idrnet_send_buf"
                      (Int -> Ptr -> Int -> JVM_IO Int)
                      (descriptor sock) ptr len

  if send_res == (-1)
   then map Left getErrno
   else pure $ Right send_res

||| Receive data from a given memory location.
|||
||| Returns on failure a `SocketError`
||| Returns on success the `ResultCode`
|||
||| @sock The socket on which to receive the message.
||| @ptr  The location containing the data to receive.
||| @len  How much of the data to receive.
recvBuf : (sock : Socket)
       -> (ptr  : BufPtr)
       -> (len  : ByteLength)
       -> JVM_IO (Either SocketError ResultCode)
recvBuf sock (BPtr ptr) len = do
  recv_res <- foreign FFI_C "idrnet_recv_buf"
                      (Int -> Ptr -> Int -> JVM_IO Int)
                      (descriptor sock) ptr len

  if (recv_res == (-1))
    then map Left getErrno
    else pure $ Right recv_res

||| Send a message stored in some buffer.
|||
||| Returns on failure a `SocketError`
||| Returns on success the `ResultCode`
|||
||| @sock The socket on which to send the message.
||| @addr Address of the recipient.
||| @port The port on which to send the message.
||| @ptr  A Pointer to the buffer containing the message.
||| @len  The size of the message.
sendToBuf : (sock : Socket)
         -> (addr : SocketAddress)
         -> (port : Port)
         -> (ptr  : BufPtr)
         -> (len  : ByteLength)
         -> JVM_IO (Either SocketError ResultCode)
sendToBuf sock addr p (BPtr dat) len = do
  sendto_res <- foreign FFI_C "idrnet_sendto_buf"
                   (Int -> Ptr -> Int -> String -> Int -> Int -> JVM_IO Int)
                   (descriptor sock) dat len (show addr) p (toCode $ family sock)

  if sendto_res == (-1)
    then map Left getErrno
    else pure $ Right sendto_res

||| Utility function to get the payload of the sent message as a `String`.
foreignGetRecvfromPayload : RecvfromStructPtr -> JVM_IO String
foreignGetRecvfromPayload (RFPtr p) =
  foreign FFI_C "idrnet_get_recvfrom_payload"
                (Ptr -> JVM_IO String)
                p

||| Utility function to return senders socket address.
foreignGetRecvfromAddr : RecvfromStructPtr -> JVM_IO SocketAddress
foreignGetRecvfromAddr (RFPtr p) = do
  sockaddr_ptr <- map SAPtr $ foreign FFI_C "idrnet_get_recvfrom_sockaddr"
                                      (Ptr -> JVM_IO Ptr)
                                      p
  getSockAddr sockaddr_ptr

||| Utility function to return sender's IPV4 port.
foreignGetRecvfromPort : RecvfromStructPtr -> JVM_IO Port
foreignGetRecvfromPort (RFPtr p) = do
  sockaddr_ptr <- foreign FFI_C "idrnet_get_recvfrom_sockaddr"
                          (Ptr -> JVM_IO Ptr)
                          p
  port         <- foreign FFI_C "idrnet_sockaddr_ipv4_port"
                          (Ptr -> JVM_IO Int)
                          sockaddr_ptr
  pure port

||| Receive a message placed on a 'known' buffer.
|||
||| Returns on failure a `SocketError`.
||| Returns on success a pair of
||| + `UDPAddrInfo` :: The address of the sender.
||| + `Int`         :: Result value from underlying function.
|||
||| @sock The channel on which to receive.
||| @ptr  Pointer to the buffer to place the message.
||| @len  Size of the expected message.
|||
recvFromBuf : (sock : Socket)
           -> (ptr  : BufPtr)
           -> (len  : ByteLength)
           -> JVM_IO (Either SocketError (UDPAddrInfo, ResultCode))
recvFromBuf sock (BPtr ptr) bl = do
  recv_ptr <- foreign FFI_C "idrnet_recvfrom_buf"
                      (Int -> Ptr -> Int -> JVM_IO Ptr)
                      (descriptor sock) ptr bl

  let recv_ptr' = RFPtr recv_ptr

  if !(nullPtr recv_ptr)
    then map Left getErrno
    else do
      result <- foreign FFI_C "idrnet_get_recvfrom_res"
                        (Ptr -> JVM_IO Int)
                        recv_ptr
      if result == -1
        then do
          freeRecvfromStruct recv_ptr'
          map Left getErrno
        else do
          port <- foreignGetRecvfromPort recv_ptr'
          addr <- foreignGetRecvfromAddr recv_ptr'
          freeRecvfromStruct recv_ptr'
          pure $ Right (MkUDPAddrInfo addr port, result + 1)

