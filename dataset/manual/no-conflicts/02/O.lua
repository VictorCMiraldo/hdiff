--- Draw a widget via a cairo context
-- @param wibox The wibox on which we are drawing
-- @param cr The cairo context used
-- @param widget The widget to draw (this uses widget:draw(cr, width, height)).
-- @param x The position that the widget should get
-- @param y The position that the widget should get
-- @param width The widget's width
-- @param height The widget's height
function base.draw_widget(wibox, cr, widget, x, y, width, height)
    if not widget.visible then
        return
    end
    -- Use save() / restore() so that our modifications aren't permanent
    cr:save()

    -- Move (0, 0) to the place where the widget should show up
    cr:translate(x, y)

    -- Make sure the widget cannot draw outside of the allowed area
    cr:rectangle(0, 0, width, height)
    cr:clip()

    -- Register the widget for input handling
    wibox:widget_at(widget, base.rect_to_device_geometry(cr, 0, 0, width, height))

    cr:restore()
end

return base

-- vim: filetype=lua:expandtab:shiftwidth=4:tabstop=8:softtabstop=4:textwidth=80
