-----------------------------------------------
-- key.lua
-- Represents a key when it is in the world
-----------------------------------------------

local Item = require 'items/item'
local Prompt = require 'prompt'
local utils = require 'utils'


function Key:keypressed( button, player )

    if button ~= 'INTERACT' then return end

    local itemNode = utils.require ('items/keys/'..self.name)
    local item = Item.new(itemNode, self.quantity)

    local message = self.info or {'You found the "'..item.description..'" key!'}
    self.touchedPlayer.character.state = 'acquire'
end

return Key
