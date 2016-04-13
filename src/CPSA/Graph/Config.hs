-- Exports a configuration that contains drawing parameters.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Graph.Config (Config(..)) where

data Config = Config
    { units :: String,          -- Unit of length
      font :: Float,            -- Font size
      stroke :: Float,          -- Stroke width
      dash :: Float,            -- Dash width
      gap :: Float,             -- Gap width in dashed lines
      mx :: Float,              -- Width of margin
      my :: Float,              -- Height of margin
      tx :: Float,              -- Distance between tree leaves
      ty :: Float,              -- Distance between tree levels
      ta :: Float,              -- Font ascent
      td :: Float,              -- Font descent
      dx :: Float,              -- Distance between strands
      dy :: Float,              -- Distance between nodes
      br :: Float,              -- Bullet radius
      compact :: Bool,          -- Generate compact format
      purge :: Bool,            -- Enable purging of traces
      scripts :: Bool }         -- Enable scripting
    deriving (Show, Read)
