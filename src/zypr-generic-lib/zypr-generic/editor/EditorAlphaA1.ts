import language from "../language/LanguageAlpha";
import backend from "../backend/BackendA";
import frontend from "../frontend/Frontend1";

export default function editor() { return frontend(backend(language())) }