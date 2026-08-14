-- Deliberately outside a matching namespace.  A name-prefix walk cannot find
-- this declaration, but module-ownership auditing must still reject it.
axiom unsoundOutsideModuleNamespace : False
