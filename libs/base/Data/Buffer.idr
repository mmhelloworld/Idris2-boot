module Data.Buffer

import System.File

export
data Buffer : Type where
     MkBuffer : Ptr -> (size : Int) -> (loc : Int) -> Buffer

export
newBuffer : Int -> JVM_IO Buffer
newBuffer size
    = do buf <- schemeCall Ptr "blodwen-new-buffer" [size]
         pure (MkBuffer buf size 0)

export
rawSize : Buffer -> JVM_IO Int
rawSize (MkBuffer buf _ _)
    = schemeCall Int "blodwen-buffer-size" [buf]

export
size : Buffer -> Int
size (MkBuffer _ s _) = s

-- Assumes val is in the range 0-255
export
setByte : Buffer -> (loc : Int) -> (val : Int) -> JVM_IO ()
setByte (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setbyte" [buf, loc, val]

export
getByte : Buffer -> (loc : Int) -> JVM_IO Int
getByte (MkBuffer buf _ _) loc
    = schemeCall Int "blodwen-buffer-getbyte" [buf, loc]

export
setInt : Buffer -> (loc : Int) -> (val : Int) -> JVM_IO ()
setInt (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setint" [buf, loc, val]

export
getInt : Buffer -> (loc : Int) -> JVM_IO Int
getInt (MkBuffer buf _ _) loc
    = schemeCall Int "blodwen-buffer-getint" [buf, loc]

export
setDouble : Buffer -> (loc : Int) -> (val : Double) -> JVM_IO ()
setDouble (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setdouble" [buf, loc, val]

export
getDouble : Buffer -> (loc : Int) -> JVM_IO Double
getDouble (MkBuffer buf _ _) loc
    = schemeCall Double "blodwen-buffer-getdouble" [buf, loc]

export
setString : Buffer -> (loc : Int) -> (val : String) -> JVM_IO ()
setString (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setstring" [buf, loc, val]

export
getString : Buffer -> (loc : Int) -> (len : Int) -> JVM_IO String
getString (MkBuffer buf _ _) loc len
    = schemeCall String "blodwen-buffer-getstring" [buf, loc, len]

export
bufferData : Buffer -> JVM_IO (List Int)
bufferData buf
    = do len <- rawSize buf
         unpackTo [] len
  where
    unpackTo : List Int -> Int -> JVM_IO (List Int)
    unpackTo acc 0 = pure acc
    unpackTo acc loc
        = do val <- getByte buf (loc - 1)
             unpackTo (val :: acc) (loc - 1)

export
readBufferFromFile : BinaryFile -> Buffer -> (maxbytes : Int) -> JVM_IO Buffer
readBufferFromFile (FHandle h) (MkBuffer buf size loc) max
    = do read <- schemeCall Int "blodwen-readbuffer" [h, buf, loc, max]
         pure (MkBuffer buf size (loc + read))

export
writeBufferToFile : BinaryFile -> Buffer -> (maxbytes : Int) -> JVM_IO Buffer
writeBufferToFile (FHandle h) (MkBuffer buf size loc) max
    = do let maxwrite = size - loc
         let max' = if maxwrite < max then maxwrite else max
         schemeCall () "blodwen-writebuffer" [h, buf, loc, max']
         pure (MkBuffer buf size (loc + max'))
