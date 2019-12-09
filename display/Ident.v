Require Lident.

Definition display_struct_name (a : unit) := Lident.intern_string "display_ctx".

Definition create_func_name (a : unit) := Lident.intern_string "create_display_ctx".

Definition update_func_name (a : unit) := Lident.intern_string "update_display_ctx".

Definition toplevel_xml_ele (a : unit) := Lident.intern_string "body".
Definition widget_xml_ele (a : unit) := Lident.intern_string "widget".
Definition param_xml_ele (a : unit) := Lident.intern_string "parameter".
Definition static_xml_ele (a : unit) := Lident.intern_string "static".
Definition event_xml_ele (a : unit) := Lident.intern_string "event".
Definition subw_xml_attr (a : unit) := Lident.intern_string "subwidget".
Definition name_xml_attr (a : unit) := Lident.intern_string "name".

Definition gui_xml_ele (a : unit) := Lident.intern_string "display".
