-----------------------------------------------
-- key.lua
-- Represents a key when it is in the world
-----------------------------------------------

local Item = require 'items/item'
local Prompt = require 'prompt'


function Key:keypressed( button, player )

    if button ~= 'INTERACT' then return end

    local itemNode = {type = 'key',name = self.name}
    local item = Item.new(itemNode, self.quantity)

    local message = {'You found the "'..self.name..'" key!'}
    self.touchedPlayer.character.state = 'acquire'
end

return Key
