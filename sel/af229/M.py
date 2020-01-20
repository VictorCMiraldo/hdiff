# -*- encoding: utf-8 -*-
{
    "name" : "Auction module",
    "version" : "1.0",
    "depends" : ["base","account","l10n_be","hr"],
    "update_xml" : [
        "security/ir.model.access.csv",
        "auction_view.xml", "auction_report.xml", "auction_wizard.xml"
    ],
    "demo_xml" : [
        "auction_demo.xml"
    ],
    "init_xml" : ["auction_sequence.xml"],
    "active": False,
    "installable": True
}
# vim:expandtab:smartindent:tabstop=4:softtabstop=4:shiftwidth=4:

