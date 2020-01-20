#!/usr/bin/env python
# -*- coding: utf-8 -*-
##############################################################################
#    
#    OpenERP, Open Source Management Solution
#    Copyright (C) 2004-2009 Tiny SPRL (<http://tiny.be>).
#
#    This program is free software: you can redistribute it and/or modify
#    it under the terms of the GNU Affero General Public License as
#    published by the Free Software Foundation, either version 3 of the
#    License, or (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU Affero General Public License for more details.
#
#    You should have received a copy of the GNU Affero General Public License
#    along with this program.  If not, see <http://www.gnu.org/licenses/>.     
#
##############################################################################

"""
OpenERP - Server
OpenERP is an ERP+CRM program for small and medium businesses.

The whole source code is distributed under the terms of the
GNU Public Licence.

(c) 2003-TODAY, Fabien Pinckaers - Tiny sprl
"""

#----------------------------------------------------------
# python imports
#----------------------------------------------------------
import sys
import os
import signal
import pwd
#----------------------------------------------------------
# ubuntu 8.04 has obsoleted `pyxml` package and installs here.
# the path needs to be updated before any `import xml`
# TODO: remove PyXML dependencies, use lxml instead.
#----------------------------------------------------------
_oldxml1 = '/usr/lib/python%s/site-packages/oldxml' % sys.version[:3]
_oldxml2 = '/usr/lib/python%s/dist-packages/oldxml' % sys.version[:3]
if os.path.exists(_oldxml1):
    sys.path.insert(0,_oldxml1)
elif os.path.exists(_oldxml2):
    sys.path.insert(0,_oldxml2)    

import release
__author__ = release.author
__version__ = release.version

# We DON't log this using the standard logger, because we might mess
# with the logfile's permissions. Just do a quick exit here.
if pwd.getpwuid(os.getuid())[0] == 'root' :
    sys.stderr.write("Attempted to run OpenERP server as root. This is not good, aborting.\n")
    sys.exit(1)

#----------------------------------------------------------
# get logger
#----------------------------------------------------------
import netsvc
logger = netsvc.Logger()

#-----------------------------------------------------------------------
# import the tools module so that the commandline parameters are parsed
#-----------------------------------------------------------------------
import tools

logger.notifyChannel("server", netsvc.LOG_INFO, "version - %s" % release.version )
for name, value in [('addons_path', tools.config['addons_path']),
                    ('database hostname', tools.config['db_host'] or 'localhost'),
                    ('database port', tools.config['db_port'] or '5432'),
                    ('database user', tools.config['db_user'])]:
    logger.notifyChannel("server", netsvc.LOG_INFO, "%s - %s" % ( name, value ))

import time

#----------------------------------------------------------
# init net service
#----------------------------------------------------------
logger.notifyChannel("objects", netsvc.LOG_INFO, 'initialising distributed objects services')

#---------------------------------------------------------------
# connect to the database and initialize it with base if needed
#---------------------------------------------------------------
import pooler

#----------------------------------------------------------
# import basic modules
#----------------------------------------------------------
import osv
import workflow
import report
import service

#----------------------------------------------------------
# import addons
#----------------------------------------------------------

import addons

#----------------------------------------------------------
# Load and update databases if requested
#----------------------------------------------------------

import service.http_server

if not ( tools.config["stop_after_init"] or \
    tools.config["translate_in"] or \
    tools.config["translate_out"] ):
    service.http_server.init_servers()
    service.http_server.init_xmlrpc()

    import service.netrpc_server
    service.netrpc_server.init_servers()

if tools.config['db_name']:
    for db in tools.config['db_name'].split(','):
        pooler.get_db_and_pool(db, update_module=tools.config['init'] or tools.config['update'])

#----------------------------------------------------------
# translation stuff
#----------------------------------------------------------
if tools.config["translate_out"]:
    import csv

    if tools.config["language"]:
        msg = "language %s" % (tools.config["language"],)
    else:
        msg = "new language"
    logger.notifyChannel("init", netsvc.LOG_INFO, 
                         'writing translation file for %s to %s' % (msg, 
                                                                    tools.config["translate_out"]))

    fileformat = os.path.splitext(tools.config["translate_out"])[-1][1:].lower()
    buf = file(tools.config["translate_out"], "w")
    tools.trans_export(tools.config["language"], tools.config["translate_modules"], buf, fileformat)
    buf.close()

    logger.notifyChannel("init", netsvc.LOG_INFO, 'translation file written successfully')
    sys.exit(0)

if tools.config["translate_in"]:
    tools.trans_load(tools.config["db_name"], 
                     tools.config["translate_in"], 
                     tools.config["language"])
    sys.exit(0)

#----------------------------------------------------------------------------------
# if we don't want the server to continue to run after initialization, we quit here
#----------------------------------------------------------------------------------
if tools.config["stop_after_init"]:
    sys.exit(0)


#----------------------------------------------------------
# Launch Servers
#----------------------------------------------------------

LST_SIGNALS = ['SIGINT', 'SIGTERM']
if os.name == 'posix':
    LST_SIGNALS.extend(['SIGUSR1','SIGQUIT'])


SIGNALS = dict(
    [(getattr(signal, sign), sign) for sign in LST_SIGNALS]
)

def handler(signum, _):
    """
    :param signum: the signal number
    :param _: 
    """
    netsvc.Agent.quit()
    netsvc.Server.quitAll()
    if tools.config['pidfile']:
        os.unlink(tools.config['pidfile'])
    logger.notifyChannel('shutdown', netsvc.LOG_INFO, 
                         "Shutdown Server! - %s" % ( SIGNALS[signum], ))
    logger.shutdown()
    sys.exit(0)

for signum in SIGNALS:
    signal.signal(signum, handler)

if tools.config['pidfile']:
    fd = open(tools.config['pidfile'], 'w')
    pidtext = "%d" % (os.getpid())
    fd.write(pidtext)
    fd.close()


netsvc.Server.startAll()

logger.notifyChannel("web-services", netsvc.LOG_INFO, 
                     'the server is running, waiting for connections...')

while True:
    time.sleep(60)

# vim:expandtab:smartindent:tabstop=4:softtabstop=4:shiftwidth=4:
