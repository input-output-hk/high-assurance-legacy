{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Data.Polynomial.Class
    ( Distribution (..)
    , revTime2
    , after
    , ftf
    , ltf
    , startingAt
    ) where

class ( Fractional prob
      , Num time
      , Monoid dist
      ) => Distribution prob time dist | dist -> prob time where
    mass     :: dist -> prob
    mean     :: dist -> Maybe time
    support  :: dist -> Maybe (time, time)
    scale    :: prob -> dist -> dist
    shift    :: time -> dist -> dist
    convolve :: dist -> dist -> dist
    before   :: dist -> dist -> dist
    residual :: dist -> dist -> dist
    endingAt :: time -> dist -> dist
    revTime  :: dist -> dist

revTime2 :: Distribution p t d => (d -> d -> d) -> d -> d -> d
revTime2 op x y = revTime $ revTime x `op` revTime y

after, ftf, ltf :: Distribution p t d => d -> d -> d
after = revTime2 before
ftf x y = before x y <> before y x
ltf x y = after x y <> after y x

startingAt :: Distribution p t d => t -> d -> d
startingAt t = revTime . endingAt (-t) . revTime
