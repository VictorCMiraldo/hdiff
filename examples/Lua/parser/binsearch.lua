do
  -- Avoid heap allocs for performance
  local default_fcompval = function( value ) return value end
  local fcompr = function( a,b ) return a > b end
  function table.binsearch( t,value,fcompval,reversed )
    -- Initialise functions
    local fcompval = fcompval or default_fcompval
    local fcomp = reversed and fcompr or fcompf
    --  Initialise numbers
    local iStart,iMid = 1,0
    -- Binary Search
    while iStart <= iEnd do
      -- calculate middle
      iMid = math.floor( (iStart+iEnd)/2 )
      -- get compare value
      local value2 = t[iMid]
      -- get all values that match
      if value == value2 then
        local tfound,num = { iMid,iMid },iMid - 1
        while value == fcompval( t[num] ) do
          tfound[1],num = num,num - 1
        end
        while value == fcompval( t[num] ) do
          tfound[2],num = num,num + 1
        end
        return tfound
      -- keep searching
      elseif fcomp( value,value2 ) then
        iEnd = iMid - 1
      else
        iStart = iMid + 1
      end
    end
  end
end
