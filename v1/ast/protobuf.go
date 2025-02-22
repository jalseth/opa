package ast

import (
	"encoding/base64"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
)

// ProtoObject accepts a Protobuf message and converts it to an ast object. Fields
// that are set to the default value are skipped during conversion.
func ProtoObject(msg proto.Message) Object {
	if msg == nil || !msg.ProtoReflect().IsValid() {
		return NewObject()
	}

	pr := msg.ProtoReflect()
	obj := newobject(pr.Descriptor().Fields().Len())
	pr.Range(func(fd protoreflect.FieldDescriptor, fv protoreflect.Value) bool {
		if protoFieldIsDefault(fd, fv) {
			return true
		}

		k, v := convertProtoField(fd, fv, false /* lazy */)
		obj.insert(k, v, false /* resetSort */)
		return true
	})

	return obj
}

func protoFieldIsDefault(fd protoreflect.FieldDescriptor, v protoreflect.Value) bool {
	// Ignore scalar fields that are not set.
	if fd.Default().Equal(v) {
		return true
	}
	// Ignore submessages that are not set.
	if (fd.Kind() == protoreflect.MessageKind || fd.Kind() == protoreflect.GroupKind) && !v.Message().IsValid() {
		return true
	}
	return false
}

func convertProtoField(fd protoreflect.FieldDescriptor, fv protoreflect.Value, lazy bool) (*Term, *Term) {
	k := StringTerm(string(fd.Name()))
	v := convertProtoValue(fd, fv, lazy)
	return k, v
}

func convertProtoValue(fd protoreflect.FieldDescriptor, fv protoreflect.Value, lazy bool) *Term {
	if fd.IsList() {
		return convertProtoList(fd, fv.List(), lazy)
	}
	if fd.IsMap() {
		return convertProtoMap(fd, fv.Map(), lazy)
	}

	// The order in the switch is based on expected frequency of usage for inputs
	// for Rego evaluation. Strings, bools, and enums are the most common.
	switch fd.Kind() {
	case protoreflect.StringKind:
		return StringTerm(fv.String())
	case protoreflect.BoolKind:
		return BooleanTerm(fv.Bool())
	case protoreflect.EnumKind:
		return StringTerm(string(fd.Enum().Values().ByNumber(fv.Enum()).Name()))
	case protoreflect.MessageKind, protoreflect.GroupKind:
		msg := fv.Message().Interface()
		if lazy {
			return NewTerm(LazyProtoObject(msg))
		}
		return NewTerm(ProtoObject(msg))
	case protoreflect.Int32Kind, protoreflect.Int64Kind, protoreflect.Sint32Kind, protoreflect.Sfixed32Kind, protoreflect.Sint64Kind, protoreflect.Sfixed64Kind:
		return IntNumberTerm(int(fv.Int()))
	case protoreflect.Uint32Kind, protoreflect.Uint64Kind, protoreflect.Fixed32Kind, protoreflect.Fixed64Kind:
		return UIntNumberTerm(fv.Uint())
	case protoreflect.DoubleKind, protoreflect.FloatKind:
		return FloatNumberTerm(fv.Float())
	case protoreflect.BytesKind:
		return StringTerm(base64.StdEncoding.EncodeToString(fv.Bytes()))
	}

	// This code branch should never be reached, all cases are covered.
	// https://pkg.go.dev/google.golang.org/protobuf/reflect/protoreflect#Value
	return nil
}

func convertProtoList(fd protoreflect.FieldDescriptor, l protoreflect.List, lazy bool) *Term {
	vals := make([]*Term, l.Len())
	for i := 0; i < l.Len(); i++ {
		vals[i] = convertProtoValue(fd, l.Get(i), lazy)
	}
	return NewTerm(NewArray(vals...))
}

func convertProtoMap(fd protoreflect.FieldDescriptor, m protoreflect.Map, lazy bool) *Term {
	obj := newobject(m.Len())
	m.Range(func(mk protoreflect.MapKey, mv protoreflect.Value) bool {
		k := convertProtoValue(fd.MapKey(), protoreflect.Value(mk), lazy)
		v := convertProtoValue(fd.MapValue(), mv, lazy)
		obj.insert(k, v, false /* resetSort */)
		return true
	})
	return NewTerm(obj)
}

// LazyProtoObject accepts a Protobuf message which is lazily converted to an ast object
// as needed. If the evaluation causes all fields to be converted, the pointer to the
// proto message is released so it can be GC'd.
//
// This approach can be more performant with larger proto messages and Rego policies that
// only access a small number of the fields in the proto. The downside is that this can
// increase memory usage in some scenarios as the proto cannot be GC'd until all of the
// in the lazy object have been converted.
func LazyProtoObject(msg proto.Message) Object {
	if msg == nil || !msg.ProtoReflect().IsValid() {
		return NewObject()
	}

	pr := msg.ProtoReflect()
	fields := make(map[string]struct{})
	pr.Range(func(fd protoreflect.FieldDescriptor, fv protoreflect.Value) bool {
		if protoFieldIsDefault(fd, fv) {
			return true
		}

		fields[string(fd.Name())] = struct{}{}
		return true
	})

	return &lazyProtoObj{
		msg:    pr,
		fields: fields,
		obj:    newobject(0),
	}
}

type lazyProtoObj struct {
	msg    protoreflect.Message
	fields map[string]struct{}
	obj    *object
}

func (l *lazyProtoObj) Len() int {
	return len(l.fields) + l.obj.Len()
}

func (l *lazyProtoObj) Hash() int {
	return l.obj.Hash()
}

func (l *lazyProtoObj) IsGround() bool {
	return true
}

func (l *lazyProtoObj) convertAndInsert(field string) (*Term, *Term) {
	fd := l.msg.Descriptor().Fields().ByName(protoreflect.Name(field))
	k, v := convertProtoField(fd, l.msg.Get(fd), true /* lazy */)

	l.obj.Insert(k, v)
	l.tidy(field)
	return k, v
}

func (l *lazyProtoObj) tidy(field string) {
	if len(l.fields) == 1 {
		l.msg = nil
		l.fields = nil
	} else {
		delete(l.fields, field)
	}
}

func (l *lazyProtoObj) Find(path Ref) (Value, error) {
	if l.fields == nil {
		return l.obj.Find(path)
	}
	if len(path) == 0 {
		return l, nil
	}

	// If the first part of the path is in the converted object, use that.
	if v := l.obj.Get(path[0]); v != nil {
		return v.Value.Find(path[1:])
	}

	// Convert and find.
	p, ok := path[0].Value.(String)
	if !ok {
		return nil, errFindNotFound
	}
	if _, ok := l.fields[string(p)]; !ok {
		return nil, errFindNotFound
	}
	_, v := l.convertAndInsert(string(p))
	return v.Value.Find(path[1:])
}

func (l *lazyProtoObj) Get(k *Term) *Term {
	if l.fields == nil {
		return l.obj.Get(k)
	}

	if s, ok := k.Value.(String); ok {
		if _, ok = l.fields[string(s)]; ok {
			_, v := l.convertAndInsert(string(s))
			return v
		}
	}

	return l.obj.Get(k)
}

func (l *lazyProtoObj) get(_ *Term) *objectElem { return nil }

func (l *lazyProtoObj) Insert(k, v *Term) {
	if l.fields == nil {
		l.obj.Insert(k, v)
		return
	}

	// Delete the key from the fields list if present.
	if s, ok := k.Value.(String); ok {
		if _, ok = l.fields[string(s)]; ok {
			l.tidy(string(s))
		}
	}

	// Then perform the insert.
	l.obj.Insert(k, v)
}

func (l *lazyProtoObj) Iter(f func(*Term, *Term) error) error {
	if l.fields == nil {
		return l.obj.Iter(f)
	}

	if err := l.obj.Iter(f); err != nil {
		return err
	}

	for field := range l.fields {
		k, v := l.convertAndInsert(field)
		if err := f(k, v); err != nil {
			return err
		}
	}

	return nil
}

func (l *lazyProtoObj) Until(f func(*Term, *Term) bool) bool {
	if l.fields == nil {
		return l.obj.Until(f)
	}

	if l.obj.Until(f) {
		return true
	}

	for field := range l.fields {
		k, v := l.convertAndInsert(field)
		if f(k, v) {
			return true
		}
	}

	return true
}

func (l *lazyProtoObj) KeysIterator() ObjectKeysIterator {
	if l.fields == nil {
		return l.obj.KeysIterator()
	}
	return &lazyProtoObjKeysIterator{
		l:  l,
		ki: l.obj.KeysIterator(),
	}
}

type lazyProtoObjKeysIterator struct {
	l    *lazyProtoObj
	ki   ObjectKeysIterator
	done bool
}

func (it *lazyProtoObjKeysIterator) Next() (*Term, bool) {
	if !it.done {
		t, ok := it.ki.Next()
		it.done = !ok
		return t, true
	}

	for field := range it.l.fields {
		k, _ := it.l.convertAndInsert(field)
		if it.l.fields == nil {
			return k, false
		}
		return k, true
	}

	// This will never be hit as the range above always returns.
	return nil, false
}

func (l *lazyProtoObj) Compare(other Value) int {
	o1 := sortOrder(l)
	o2 := sortOrder(other)
	if o1 < o2 {
		return -1
	}
	if o1 > o2 {
		return 1
	}
	return l.force().Compare(other)
}

/// --------------------------------------------------------- ///
///         All other methods require full conversion         ///
/// --------------------------------------------------------- ///

func (l *lazyProtoObj) force() Object {
	for field := range l.fields {
		l.convertAndInsert(field)
	}
	return l.obj
}

func (l *lazyProtoObj) Copy() Object {
	return l.force().Copy()
}

func (l *lazyProtoObj) Diff(other Object) Object {
	return l.force().Diff(other)
}

func (l *lazyProtoObj) Intersect(other Object) [][3]*Term {
	return l.force().Intersect(other)
}

func (l *lazyProtoObj) Foreach(f func(*Term, *Term)) {
	l.force().Foreach(f)
}

func (l *lazyProtoObj) Filter(filter Object) (Object, error) {
	return l.force().Filter(filter)
}

func (l *lazyProtoObj) Map(f func(*Term, *Term) (*Term, *Term, error)) (Object, error) {
	return l.force().Map(f)
}

func (l *lazyProtoObj) MarshalJSON() ([]byte, error) {
	return l.force().(*object).MarshalJSON()
}

func (l *lazyProtoObj) Merge(other Object) (Object, bool) {
	return l.force().Merge(other)
}

func (l *lazyProtoObj) MergeWith(other Object, conflictResolver func(v1, v2 *Term) (*Term, bool)) (Object, bool) {
	return l.force().MergeWith(other, conflictResolver)
}

func (l *lazyProtoObj) String() string {
	return l.force().String()
}

func (l *lazyProtoObj) Keys() []*Term {
	return l.force().Keys()
}
